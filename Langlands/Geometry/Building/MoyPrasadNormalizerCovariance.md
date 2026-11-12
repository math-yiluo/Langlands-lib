# Normalizer covariance on the apartment

This derived construction gives actual normalizer covariance of the unchanged original Moy–Prasad subgroups, and two generator-level conjugation bounds. The apartment, centralizer inclusion, rational-point group, subgroups and depths remain the supplied original ones.

`conj_mem_moyPrasad_normalizer` proves containment under an actual normalizer point `n`. The supplied `IsNormalizerStable` preserves the original centralizer-depth image. The published `conj_mem_filtration` sends each actual root-depth generator to the root with direction `weylAction n a`, at the same depth and the point `n • x`; the published Weyl action preserves the actual relative-root set. The supremum formula for the original sharp filtration then proves the containment on the entire original Moy–Prasad subgroup. No apartment axioms or other centralizer-filtration axioms are needed for this step.

`moyPrasadNormalizerFamily` packages this containment as an actual `CovariantSubgroupFamily`. Applying containment to `n⁻¹` gives the reverse inclusion, proving the exact map equality `moyPrasad_map_conj_normalizer`. `moyPrasadNormalizerEquiv` restricts the actual ambient conjugation automorphism to this equality, giving a multiplicative equivalence between the two original subgroups.

`conjugate_root_mem_moyPrasad_of_nonopposite` applies V3 to directions that are not negative real multiples. The conjugating element has depth zero. The resulting root-depth bounds are `p·0+q·r ≥ r`, since `q` is a positive integer and `r` is nonnegative. Thus the commutator lies in the original Moy–Prasad subgroup, and multiplying by the original second root element gives the conjugate there.

`conjugate_image_mem_moyPrasad` uses the supplied `IsRootCompatible` at depths `r` and zero, applied to the inverse middle element. Its commutator belongs to the full original block at depth `r`. Multiplying by the original middle element gives the conjugate inside the original Moy–Prasad subgroup.

All results hold at arbitrary nonnegative depths and universes. The latter two bounds use respectively V3 and root compatibility, as explicit in their hypotheses. They do not establish every negative proportional root case, sharp-fixer normalization, covariance on the reduced building, centralizer-filtration existence or the host simultaneous normal basis. The provenance is internal derivation from the original definitions, published normalizer/root covariance and V3, and the supplied centralizer-filtration axioms.
