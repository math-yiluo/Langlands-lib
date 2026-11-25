# Finite coefficient models of separated finitely presented groups

This internal construction supplies the separated target-group
model in the arbitrary-base limit reduction for reductive group
monomorphisms. Its provenance is the combination of published general scheme
approximation, group-law descent and eventual separation; it does not require
an affine target.

`SeparatedGroupModel R A G` consists of a finitely generated `R`-subalgebra
of the arbitrary commutative `R`-algebra `A`, an actual separated group scheme
with quasi-compact locally finitely presented structure morphism over that
subalgebra, and a group scheme isomorphism recovering `G` after base change.
`exists_separatedGroupModel` constructs such a model containing any prescribed
finite subset of `A`, and `separatedGroupModel` chooses one with no prescribed
coefficients.

The underlying separated, finitely presented scheme first descends to a
finitely generated coefficient subalgebra `T` by
`exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`.
The published `Langlands.GroupScheme.subalgebraDescent` descends the actual
group law after passing to a finitely generated `T`-subalgebra `U`. The
resulting structure morphism remains quasi-compact, quasi-separated and
locally finitely presented by its pullback square.

Separation of the supplied group transfers across the comparison isomorphism
to the base change of this model. The published eventual-separation theorem
then gives a finitely generated `U`-subalgebra `V` where the model is separated.
Restriction of scalars makes `V` a finitely generated `R`-subalgebra. The
iterated/direct group scheme pullback comparison composes with the earlier
isomorphism to give the required recovery isomorphism. The coefficient tower
preserves the prescribed finite subset.

This construction does not descend a homomorphism, monicity or reductivity,
and does not prove the reductive monomorphism closed-immersion theorem.
