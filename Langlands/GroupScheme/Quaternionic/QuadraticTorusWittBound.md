# Split tori in the quaternionic isometry group are bounded by the Witt index

Author: Worker 350.

Module `Langlands.GroupScheme.Quaternionic.QuadraticTorusWittBound`.

## Setting

`K` is a field (finite or infinite, of any characteristic), `D` a finite-dimensional
division `K`-algebra, `σ : FirstKindInvolution K D`, `n` a finite index type and `q` a
`σ`-quadratic form on row vectors `D^n`, i.e. a class in `M_n(D) / {x - ᵗx^σ}` (published in
`Quaternionic.Forms`). `Q = Quotient.out q` is a representing matrix, `τ = σ.matrix n` is the
involution `x ↦ ᵗx^σ` of `M_n(D)`, and `O(q) = σ.isometryGroup q` is the published closed
subgroup of the unit group of `M_n(D)` cut out by the condition that the defect
`u Q τ(u) - Q` lies in `R ⊗ {x - τ x}` (published in `Quaternionic.GroupSchemes` and
`Quaternionic.IsometryCut`).

## Results

- `coeffTensor_mem_of_mem_baseChange`: for a `K`-subspace `M` of a `K`-algebra `A` and an
  element of `K[Λ] ⊗ A` lying in the scalar extension of `M`, every coefficient
  (`MatrixNormOneSplitRank.coeffTensor`) lies in `M`.
- `coeffTensor_zero_defect_sum`: for an involution `τ` of `A`, the constant coefficient of the
  defect of `∑_{m ∈ s} Xᵐ ⊗ eₘ` is `∑_{m + p = 0} eₘ Q τ(eₚ) - Q`.
- `sandwich_mem_alternatingSubspace`: `z ↦ a z τ(a)` preserves `{x - τ x}`.
- `sandwich_coefficient`: if `e` is a family of orthogonal idempotents, `S` is a finite set of
  indices no two of which (possibly equal) add up to `0`, and `f = ∑_{p ∈ S} eₚ`, then
  `f (∑_{m + p = 0} eₘ Q τ(eₚ) - Q) τ(f) = -(f Q τ(f))`.
- `quadraticValue_eq_zero_of_vecMul_eq`: if `f Q τ(f) ∈ {x - τ x}` and the row vector `x`
  satisfies `x f = x`, then `q(x) = 0`.
- `card_le_quadraticWittIndex_of_idempotents`: a family of orthogonal idempotent matrices,
  nonzero on a finite set `S`, with `f Q τ(f) ∈ {x - τ x}` for `f = ∑_{p ∈ S} eₚ`, gives
  `|S| ≤ σ.quadraticWittIndex q`. A nonzero row `w_m` of each `e_m` (`m ∈ S`) satisfies
  `w_m e_p = δ_{mp} w_m`; these rows are `D`-linearly independent, their span is fixed by `f`,
  hence totally singular of dimension `|S|`.
- `defect_affinePoint_mem`: for every commutative `K`-algebra `R`, the image in
  `(R ⊗ M_n(D))ˣ` of an `R`-point of `O(q)` has defect in `R ⊗ {x - τ x}`.
- `card_le_quadraticWittIndex_of_mono`: if `t : 𝔾ₘ^I → O(q)` is a homomorphism whose composite
  with the inclusion `O(q) → GL₁(M_n(D))` is a monomorphism on underlying schemes, then
  `|I| ≤ σ.quadraticWittIndex q`.
- `splitRank_isometryGroup_le`: `splitRank O(q) ≤ σ.quadraticWittIndex q`.
- `splitRank_connectedIsometryGroup_le`: if `O(q)` is smooth, then
  `splitRank O(q)⁰ ≤ σ.quadraticWittIndex q`.

## Proof of the torus bound

Let `j = t ≫ ι` be the composite torus in the matrix unit group and `u ∈ (K[ℤ^I] ⊗ M_n(D))ˣ`
its universal (Laurent-polynomial) point, `FiniteAlgebraTorusWeights.universalUnit j`.
By `defect_affinePoint_mem` the defect of `u` lies in `K[ℤ^I] ⊗ {x - τ x}`; since `O(q)` is a
subgroup at every algebra (`IsometryCut.isometrySubgroup`) the same holds for `u⁻¹`. The
published weight decomposition (`universalUnit_inv_eq_sum`) writes
`u⁻¹ = ∑_{m ∈ supp} Xᵐ ⊗ eₘ` with orthogonal nonzero idempotents `eₘ`
(`weightElement_mul`, `weightElement_ne_zero`), and, since `j` is a monomorphism, the weight
support generates `ℤ^I` (`closure_weightSupport`).

The published `HermitianWeights.exists_nonopposite_subfamily` chooses a subfamily `S` of the
support in which no two (possibly equal) weights add up to `0` and which represents every
nonzero weight up to sign. Zero contributes nothing to the generated lattice, so
`HermitianWeights.card_le_of_generators_up_to_sign` gives `|I| ≤ |S|`.
Taking the constant coefficient of the defect of `u⁻¹` gives
`∑_{m + p = 0} eₘ Q τ(eₚ) - Q ∈ {x - τ x}`. Sandwiching by `f = ∑_{p ∈ S} eₚ` kills every term
with `m + p = 0` (one of `m, p` is outside `S`), so `f Q τ(f) ∈ {x - τ x}`, and
`card_le_quadraticWittIndex_of_idempotents` gives `|S| ≤` Witt index.

The split-rank bound takes the supremum over closed split tori: the composite of the closed
immersion `t` with the closed inclusion of `O(q)` is a closed immersion, hence a
monomorphism (`IsClosedImmersion.iff_isFinite_and_mono`). For `O(q)⁰` the published
`splitRank_le_of_isClosedSubgroup` applied to the closed identity-component inclusion reduces
to `O(q)`.

## Provenance and scope

This is an internal derived module: it combines the published universal weight
decomposition of tori in finite-algebra unit groups, the nonopposite-subfamily lemmas of
`Torus.HermitianWeightIsotropy`, and the totally singular subspace bound
`IsTotallySingular.finrank_le_quadraticWittIndex`. It mirrors the classical argument that
weight spaces of a split torus of an orthogonal group with nonopposite weights are totally
singular. Working with the universal point rather than rational points, it needs no
infinitude of `K`. No nondegeneracy, centrality, type or characteristic hypothesis is used.
Only the upper bound is proved here.
