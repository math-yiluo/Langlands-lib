# The local E7 exclusion and the remaining E6 marking

`TitsIndexData.HasRankOneE6BranchIndex` is a predicate on actual index data
for an affine, locally finite type group scheme over an arbitrary field.
It records an equivalence of the entire vertex type with `Fin 6` that
preserves every ordered E6 Cartan entry and distinguishes exactly
vertex 1 in Mathlib's numbering. It also requires triviality of the full
absolute Galois star action. In the reduction below this property is
applied to a local group of split rank one.

`TitsIndexData.not_E7_branch_mark` applies to a simply connected group over
a nonarchimedean local field. An exact E7 Cartan numbering with precisely
vertex 1 distinguished and trivial full star would give the actual
anisotropic kernel a central division norm-one presentation of reduced
degree seven. The published E7 theorem provides a group-scheme
automorphism of that kernel moving the full centre. The published
norm-one automorphism theorem and the local opposite-algebra degree bound
imply that every automorphism of this kernel fixes the full centre.
These two conclusions contradict each other in every field and residue
characteristic.

`localRankOneTitsIndex_or_E6_or_residual_of_componentFactor` assumes
`SemisimpleTitsComponentFactorStatement` and takes actual index data for a
simply connected, absolutely almost-simple local group of split rank one.
The published absolute Cartan classification identifies the entire actual
matrix with one of the irreducible Cartan types. The published local
anisotropic type-A theorem and component realization give the needed
component bounds. The shared nine-family reduction takes exclusions of
the two branch-marked E types as arguments. If the exact E6 predicate
holds, it gives the E6 alternative. Otherwise its negation supplies the
E6 input to the shared reduction and the theorem above supplies the E7
input. The resulting disjunction has the five desired index alternatives,
the E6 branch marking, and the previously defined higher-B, G2 and D4
residual patterns.

The construction is an internal composition of the published E7,
norm-one and finite Cartan proofs and the existing local case analysis.
The full enumeration still needs the component realization and the
exclusions of the remaining residual patterns.
