# Splitting a multiplicative-type residue fibre at an etale point

Worker 875.

`Langlands.GroupScheme.ExtensionReduction.etaleSpecialSplitting R G p`
constructs an actual etale `R`-algebra and a point above the given prime `p`
whose residue fibre of `G` has an actual diagonalizable presentation. The
hypothesis is the field-level `IsMultiplicativeType` predicate for the
pullback of `G` along the canonical map `R -> p.asIdeal.ResidueField`.
There are no flatness, finite-presentation or affineness assumptions on `G`,
and `R` need not be noetherian.

The resulting `EtaleSpecialSplitting` records the ring, its commutative-ring
and `R`-algebra structures and etale property, the point and its image equation,
a finitely generated full abelian character group, and a group-scheme
isomorphism. Its source is the actual residue-field pullback of the actual
base change of `G` to that algebra; its target is the affine group-algebra
model of the recorded character group. Torsion in the character group is
retained.

`nonempty_etaleSpecialSplitting` applies the published finite Galois splitting
theorem to the specified residue fibre. The published
`Langlands.CommutativeAlgebra.exists_etale_residue_extension` realizes the
finite separable splitting field as the actual residue field of a point of
an etale `R`-algebra. Its residue-field isomorphism and compatibility with the
map from `R` identify the two pullback routes. The actual group pullback
comparisons and the diagonalizable base-change isomorphism transport the
splitting to this residue point. The prime contraction equality proves that
the point lies over `p`. `etaleSpecialSplitting` chooses these data.

`EtaleSpecialSplitting.noetherian` proves that the resulting algebra is
noetherian whenever `R` is, using finite type of an etale algebra. This fact
supports subsequent localization and completion.

This is an internal composition of the two published existence theorems and
actual base-change comparisons. It does not construct a strict henselization,
prove that the whole group is of relative multiplicative type, or prove the
host fpqc extension theorem. No field extension or deformation theorem about
extensions of groups is assumed.
