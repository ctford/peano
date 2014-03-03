data MultipleOf : Nat -> Nat -> Type where
  NoneOf : (m : Nat) -> MultipleOf m Z
  Next : MultipleOf m n -> MultipleOf m (n + m)

add : MultipleOf m a -> MultipleOf m b -> MultipleOf m (a + b)
add (NoneOf _) y = y
add (Next x) y ?= add x (Next y)

---------- Proofs ----------


Main.add_lemma_1 = proof
  intros
  rewrite plusAssociative n m b
  rewrite sym $ plusCommutative m b
  trivial
