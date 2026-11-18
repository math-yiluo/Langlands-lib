# Linear reductivity along injective affine coordinate pullbacks

Let `f : G ⟶ H` be a homomorphism of affine group schemes over a field with
injective coordinate pullback. For each actual finite-coordinate representation
`ρ` of `H`, `MatrixRepresentation.isStableSubspace_restrict_iff_of_injective_pullback`
identifies the stable subspaces of `ρ` and of its restriction along `f`.
`IsLinearlyReductive.of_injective_pullback` then deduces linear reductivity of `H`
from that of `G` in the exact finite-coordinate condition used by Nagata's theorem.

The proof uses the universal coefficient criterion of `AffineCoefficients`.
The universal matrix of the restriction is the entrywise pullback of the
original universal matrix. Since the coordinate pullback is an injective linear
map of vector spaces over the field, it has a linear left inverse. Composing
any functional on the target group's coordinates with this left inverse
produces a functional on the source group's coordinates with the same extracted
matrix. The universal criterion gives reflection of stability, and the existing
restriction theorem gives preservation. The two representations therefore have
the same simple stable subspaces in the supremum defining linear reductivity.

`LinearlyReductiveSchematicQuotientStatement` states the geometric form over
every field. If the actual affine group homomorphism is schematically dominant,
its affine presentations identify it with the spectrum of the coordinate
pullback. Schematic dominance makes the pullback on global sections injective.
Naturality of `ΓSpecIso` transfers this injectivity to the coordinate
homomorphism. The theorem `linearlyReductiveSchematicQuotient` applies the
injective-pullback result to this homomorphism.

This is a derived coefficient lemma for the schematic images in the proof of
structural necessity in Nagata's theorem. Its proof applies over any field and
compares stability on all affine tests, including nonreduced algebras.
