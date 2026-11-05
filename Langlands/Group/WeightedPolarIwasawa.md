# Weighted parabolic coverage from Hermitian remainders

This is an internal derived argument for the parabolic covering step. It combines
the existing matrix block subgroup with integer diagonal weights, Hermitian
symmetry and compactness. Its provenance is the elementary calculation and
compact subsequence argument below; it introduces no new literature assertion.

The scalar field `𝕜 : Type u` is any `RCLike` field, the matrix index type `n`
is any finite type with decidable equality, and `A : Type v` is any group
equipped with a topology. The universes of `𝕜` and `A` are independent. The
empty matrix index type is allowed.

The lemma `limit_entry_eq_zero` takes nonzero real parameters tending to zero
and a convergent sequence of matrices `b`. If
`diag(t_m ^ w_i) * b_m` is Hermitian, its entries satisfy
`(b_m)ᵢⱼ = t_m ^ (w_j - w_i) * star((b_m)ⱼᵢ)`.
For `w_i < w_j`, the scalar factor tends to zero, while the conjugated entry
converges. Uniqueness of the limit forces the limiting `(i,j)` entry to vanish.
All integer weights, including negative and equal weights, are permitted.

The definition `weightedParabolicSubgroup ρ w` is the comap along the group
homomorphism `ρ : A →* GL n 𝕜` of the published
`GeneralLinear.blockParabolicSubgroup 𝕜 w`. Thus its elements are exactly
those `a` whose matrix `ρ a` has zero `(i,j)` entry whenever `w i < w j`.
It makes no assertion that this subgroup comes from a geometric parabolic.

The theorem `mul_compact_eq_univ_of_hermitian` assumes:

- `ρ` is continuous and `K` is a compact subgroup of `A`;
- every `x : A` has a `k ∈ K` for which `ρ (x * k⁻¹)` is Hermitian;
- `t_m` is a sequence of nonzero real numbers tending to zero; and
- elements `D_m : A` satisfy
  `ρ D_m = diag((t_m : 𝕜) ^ w_i)`.

It proves the literal ordered pointwise product
`weightedParabolicSubgroup ρ w * K = Set.univ`.
The Hermitian hypothesis does not require positivity. The diagonal sequence is
an explicit hypothesis; it is not inferred from an arbitrary representation.

For fixed `g`, choose `k_m ∈ K` with
`ρ (D_m * g * k_m⁻¹)` Hermitian. The compact set `ρ '' K` has a convergent
subsequence `ρ k_{φ(m)} → ρ k₀` with `k₀ ∈ K`. The matrix units carry their
usual topology induced by the pair of matrix and inverse matrix. This space is
first countable, as the proof checks using the finite products of the scalar
topology and the units embedding. Continuous multiplication and inversion give
`ρ g * (ρ k_{φ(m)})⁻¹ → ρ g * (ρ k₀)⁻¹`.

Apply `limit_entry_eq_zero` with the subsequence of real parameters. The
Hermitian relation implies that `g * k₀⁻¹` belongs to the weighted subgroup.
The identity `(g * k₀⁻¹) * k₀ = g` then supplies the desired two factors.
Only the matrix image needs a convergent subsequence: the theorem requires
neither first countability of `A` nor continuous group operations on `A`, and
it requires no injectivity or closed image assumption on `ρ`.

The full archimedean Iwasawa theorem still requires construction of an
appropriate compact subgroup, maximality, a compatible realization and diagonal
sequence for every actual rational parabolic, and comparison of that
parabolic's point-image subgroup with this weighted comap. This module does
not assert or assume those conclusions as a closing theorem.
