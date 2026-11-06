# Parabolic-radical images in normal subgroups containing relative roots

Author: Worker 1331.

This internal comparison works over an arbitrary field `k : Type u`. The
ambient affine group scheme `G` is connected reductive, `i : S.toGrp ⟶ G`
is an actual maximal split torus, and `K` is an abstract normal subgroup of
`G(k)` containing every actual relative-root subgroup at `i`. The local
root-ray disjointness condition is required for every cocharacter of `S`.
Split-torus conjugacy is also an explicit input throughout.

For an arbitrary cocharacter `ζ` of `G`,
`dynamicUnipotent_le_normalSubgroup_of_root_groups` applies the published
`exists_innerIso_comp_eq_cocharacter` to conjugate `ζ` into `S`. The published
disjoint-ray generation theorem puts the conjugated radical in `K`.
`Dynamic.mem_unipotent_conj` identifies the conjugated point, and normality of
`K` transports it back. This proves containment for the whole actual dynamic
radical, not just for its tangent weights.

`map_dynamicUnipotent_le_normalSubgroup_of_root_groups` applies the published
`Dynamic.unipotent_le_comap` to any group-scheme homomorphism `f : H ⟶ G`.
No injectivity or normality condition on `f` is needed.

`parabolicRadical_range_le_normalSubgroup_of_root_groups` additionally assumes
connected reductivity of the source `H`, `ParabolicDynamicStatement` and
`DynamicCentralizerReductiveStatement`. For any actual parabolic embedding
`p : P ⟶ H` and supplied radical `r : U ⟶ P` satisfying
`LeviSubgroup.IsGeometricUnipotentRadical r`, the parabolic-dynamic input
supplies a ground-field cocharacter `ζ` presenting `p`. The canonical affine
representative of its centralizer is connected reductive by the centralizer
input. The published
`Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer` then
identifies the full ambient radical image with `Dynamic.unipotent ζ` on every
test scheme. The preceding functorial containment yields the rational-point
range inclusion for `r ≫ p ≫ f`.

`parabolicRadicalPointsToNormalSubgroup` is the induced group homomorphism
`U(k) → K`. Its underlying map is precisely the actual rational-point map
of `r ≫ p ≫ f`; the preceding range inclusion supplies the proof that each
value lies in `K`. It retains all the same structural and root hypotheses.

The provenance is internal: this module composes the cited Library proofs
without introducing a new assertion from original literature. It proves no
structural input assumed above and no local Kneser–Tits theorem. In the main
factor target, normality of the ambient root-generated subgroup and all
retained structural inputs still require proofs before this comparison can be
used unconditionally.
