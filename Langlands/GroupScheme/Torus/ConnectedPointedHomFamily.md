# Pointed families of homomorphisms from diagonalizable groups

This internal derived module applies `ConnectedCoefficientRigidity` to natural
families on algebra points. Fix a field `k`, affine group schemes `G` and `H`
with `H` connected, and an abelian group `Λ`. A family assigns to an `H(A)` point
and a character `Λ → Aˣ` a point of `G(A)`, naturally in every `k`-algebra `A`.
If the family is multiplicative in the character and trivial at the identity of
`H`, then `eq_one_of_connected_pointed_family` proves that it is identically
trivial. There are no smoothness, reducedness, or finite type hypotheses.

The proof uses the universal `H` point over its coordinate algebra `R = O(H)`
and the universal character over `R[Λ]`. Naturality and multiplicativity make
the resulting `G(R[Λ])` point multiplicative. Evaluation of `R` at the identity
of `H` specializes this point to the identity. The spectrum of `R` is connected
because it is isomorphic to `H`; the coefficient rigidity theorem therefore
makes the universal point trivial. Finally the universal property of the group
algebra specializes it to every supplied pair of points.

The result is a direct internal consequence of the coefficient rigidity lemma;
it is an auxiliary tool for the commutator-family proof of the normalizer
clause of `TorusCentralizerNormalizerStatement` and does not
assert a separately quoted literature result.
