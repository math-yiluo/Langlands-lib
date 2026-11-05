# Weighted covering after an arbitrary change of basis

This internal derived extension of `WeightedPolarIwasawa` removes the requirement
that a diagonalizing basis preserve the adjoint. Let `ρ` be a continuous matrix
representation of a topologized group `A`, let its range be closed under the
matrix adjoint, and let `K` be a compact subgroup with Hermitian right remainders
for every element of `A`. The scalar field is any `RCLike` field in universe `u`;
`A` has an independent universe `v` and an arbitrary topology.

`conjugatedRepresentation ρ B` changes basis by an arbitrary matrix unit `B`,
giving `g ↦ B⁻¹ ρ(g) B`. Suppose a sequence `D_m` in the original group has matrices
conjugate by `B` to `diag(t_m ^ w_i)`, for nonzero real `t_m` tending to zero and
integer weights `w_i`.

For a fixed `g`, use adjoint stability to lift `star (ρ(D_m))` to the original
group. The Hermitian remainder property then gives `k_m ∈ K` such that
`star (ρ(D_m)) ρ(g k_m⁻¹)` is Hermitian. Congruence by `B` gives a Hermitian matrix
`diag(t_m ^ w_i) C_m`, where `C_m = star B · ρ(g k_m⁻¹) · B`.
Compactness of the represented image of `K` supplies a convergent subsequence
whose limit has an actual preimage `k ∈ K`. The imported entry-limit argument
shows that `C = star B · ρ(g k⁻¹) · B` belongs to the weight-block parabolic.
This is `exists_congruence_block_remainder`.

Apply this first at `g = 1`, obtaining `k₀ ∈ K` and a block matrix `C₀`.
For arbitrary `g`, apply it at `k₀⁻¹ g`, obtaining `k ∈ K` and a block matrix `C`.
Their product `C₀⁻¹ C` is `B⁻¹ ρ(g k⁻¹) B`: both the adjoint change of basis and
the fixed shift cancel. Subgroup closure therefore puts `g k⁻¹` in the block
comap under `conjugatedRepresentation ρ B`. The factorization
`g = (g k⁻¹) k` proves `conjugated_mul_compact_eq_univ_of_hermitian`, with the
weighted parabolic on the left and the original `K` on the right.

The proof uses only the earlier entry-limit lemma, compact sequential extraction
in matrix units, Hermitian congruence and group identities; it introduces no new
literature assertion. The diagonalizing basis need not be unitary, and the changed
representation need not have adjoint-stable range. Adjoint stability of the
original image, compactness, Hermitian remainders and a represented conjugate
diagonal sequence remain explicit hypotheses. Actual reductive self-adjoint
realization and geometric-parabolic comparison remain separate obligations for
the full archimedean Iwasawa existence theorem.
