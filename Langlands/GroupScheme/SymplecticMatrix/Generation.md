# Generation and irreducibility of symplectic matrix groups

This internal module collects matrix facts about Mathlib's `symplecticGroup l S`, the
matrices `M` over a commutative ring `S` indexed by `l ⊕ l` with `M J Mᵀ = J`, where
`J = [[0, -1], [1, 0]]` (Mathlib's `Matrix.J`). The split symplectic group scheme
`SymplecticMatrix.groupScheme` in `SymplecticMatrix.Basic` has these matrices as its
points. Later modules use the facts here to prove that the group scheme is connected and
that its geometric unipotent radical is trivial. This module states nothing about group
schemes.

## Block matrices (any commutative ring)

* `upper Y = [[1, Y], [0, 1]]` and `lower Z = [[1, 0], [Z, 1]]`. They are symplectic when
  `Y`, respectively `Z`, is symmetric (`upper_mem`, `lower_mem`). They satisfy
  `upper Y * upper Y' = upper (Y + Y')`, the same rule for `lower`, `upper 0 = 1` and
  `lower 0 = 1`.
* `levi A = [[A, 0], [0, (A⁻¹)ᵀ]]` for `A : GL l S`. It is always symplectic
  (`levi_mem`) and multiplicative (`levi_mul`).
* `map_upper`, `map_lower` and `map_levi` say that these constructions commute with
  applying a ring homomorphism entrywise.
* `transvection u = 1 + u (uᵀ J)` for a column vector `u` (written
  `vecMulVec u (u ᵥ* J)`). It is symplectic (`transvection_mem`) and acts by
  `w ↦ w + ((uᵀ J) w) u` (`transvection_mulVec`). The proof uses that the standard
  form is alternating, `uᵀ J u = 0` (`dotProduct_vecMul_J_self`). This holds in every
  characteristic, so the proof never divides by `2`.

## Over a field

* `exists_isSymm_isUnit_add_mul`: if square matrices `A`, `C` over a field have no common
  nonzero kernel vector and `Aᵀ C = Cᵀ A`, then `A + X C` is invertible for some symmetric
  `X`. **This statement and its proof are a verbatim copy** of the private Mathlib lemma
  `SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot` in
  `Mathlib/LinearAlgebra/SymplecticGroup.lean`. Mathlib uses it on the way to
  `SymplecticGroup.det_eq_one`. Mathlib's version is private, so it cannot be imported,
  and the copy is needed.
* `fromBlocks_eq_lower_mul_levi_mul_upper`: a symplectic matrix `[[a, B], [C, D]]` with
  invertible `a` has symmetric `C a⁻¹` and equals
  `lower (C a⁻¹) * levi a * upper (a⁻¹ B)`. The proof is a direct block computation from
  the three block identities of `SymplecticGroup.fromBlocks_mem_iff`.
* `exists_eq_upper_mul_lower_mul_levi_mul_upper` (big-cell decomposition): every
  symplectic matrix `M` over a field is `upper X * lower Z * levi A * upper Y` with
  symmetric `X`, `Z`, `Y`. Proof: `M` is invertible because its determinant is `1`
  (Mathlib's `SymplecticGroup.det_eq_one`), so its left blocks `A`, `C` have no common
  kernel vector. Choose symmetric `X` as above with `A + X C` invertible. Then
  `upper X * M` has invertible upper-left block, so it factors by the previous lemma.
  The last factor is symplectic, so `Y` is symmetric. Replacing `X` by `-X` gives the
  decomposition.
* `eq_top_of_forall_mulVec_mem` (irreducibility): a nonzero subspace of `l ⊕ l → F`
  that is stable under every symplectic matrix is the whole space. Proof: take a nonzero
  `w` in the subspace. Then `J w ≠ 0`, because `J² = -1`. For every `u` with
  `(uᵀ J) w ≠ 0`, `transvection u * w - w` is a nonzero multiple of `u`, so `u` lies in
  the subspace. Choose a basis vector `u₀` with `(u₀ᵀ J) w ≠ 0`. A vector `u` with
  `(uᵀ J) w = 0` is the difference of `u + u₀` and `u₀`, which both lie in the
  subspace.

## Provenance

These are standard facts about the split symplectic group. As noted above, the copied
lemma comes from Mathlib. The block computations and the transvection argument were
written for this module.
