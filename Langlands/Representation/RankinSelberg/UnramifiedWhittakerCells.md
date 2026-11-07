# Torus values of spherical Whittaker functions

Author: Worker 1797. Module `Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells`,
namespace `Langlands.RankinSelberg.UnramifiedWhittaker`.

This internal helper module serves the proof of
`Langlands.RankinSelberg.UnramifiedSphericalVectorStatement`
(see `UnramifiedSphericalVectorProof.md`). It states no new proposition.

## Setting

`F` is a field with a valuation `v : Valuation F Γ₀`, `O = v.integer`, and
`ϖ : Fˣ` is a unit (a uniformizing element where stated). `K = GL_(n+1)(O)` is the
published `integralSubgroup v.integer n`. `torus ϖ lam` is the published
`diag(ϖ^(lam 0), …, ϖ^(lam n))` of `Langlands.Representation.Whittaker.Iwasawa`,
and `θ : upperUnipotent (n + 1) F →* ℂˣ` is a character of the upper unipotent
group. `IsIntegrallyTrivial v θ` is the published condition of
`Whittaker/Spherical` that `θ` is trivial on integral unipotent matrices.
The functions `f : GL_(n+1)(F) → ℂ` considered satisfy

- `f (u * g) = θ u * f g` for upper unipotent `u` (equivariance), and, where stated,
- `f (g * k) = f g` for `k ∈ K` (right `K`-invariance).

The coset representatives are the published ones of
`Langlands.Representation.Unramified.MinusculeCosets`: for a subset `S`,
`cosetRep ϖ S c = radicalElement S c * subsetTorus ϖ S`, where
`radicalElement S c = 1 + ∑ c_ab E_ab` over the radical pairs `a ∈ S`, `b ∉ S`,
`a < b`, and `subsetTorus ϖ S = torus ϖ (subsetExponent S)` with
`subsetExponent S` the indicator vector `1_S`. `labelledRep ϖ σ α` takes the radical
entries from labels through `σ : Λ → F`; `CosetIndex Λ (n + 1) i` is the published
index type (a subset of size `i` and a label for each radical pair).

## Torus arithmetic

- `torus_mul_torus`: `torus ϖ lam * torus ϖ mu = torus ϖ (lam + mu)`.
- `torus_conj_apply`: the `(a, b)` entry of `t g t⁻¹`, `t = torus ϖ lam`, is
  `ϖ^(lam a) g_ab ϖ^(-lam b)`.
- `torus_conj_mem_upperUnipotent`: conjugation by a torus element preserves the
  upper unipotent group (zero below the diagonal, one on it).

## Integrality of conjugated radical elements

- `radicalElement_entry_mem`: if the radical entries are integral, every entry of
  `radicalElement S c` is integral.
- `torus_conj_radicalElement_mem`: if `v ϖ ≤ 1`, `lam` is antitone (dominant) and
  the radical entries are integral, then `t * radicalElement S c * t⁻¹ ∈ K`. Both
  the matrix and its inverse `t * radicalElement S (-c) * t⁻¹` have integral entries
  by the published `torus_conj_entry_mem`, because the entry in position `a ≤ b`
  is multiplied by `ϖ^(lam a - lam b)` with `lam a ≥ lam b`.

## Values at dominant translates of coset representatives

- `eval_integral_unipotent_mul`: for integrally trivial `θ`, an equivariant `f`
  satisfies `f (u * g) = f g` whenever `u` is unipotent and integral.
- `eval_torus_mul_cosetRep`: for dominant `lam`, `v ϖ ≤ 1` and integral radical
  entries, `f (ϖ^lam * cosetRep ϖ S c) = f (ϖ^(lam + 1_S))`. Proof:
  `ϖ^lam * radicalElement S c * subsetTorus ϖ S = u * ϖ^(lam + 1_S)` with
  `u = ϖ^lam * radicalElement S c * ϖ^(-lam)`, which is unipotent and integral.
- `eval_torus_mul_labelledRep`: the same for `labelledRep ϖ σ α` when all labels
  `σ x` are integral.
- `sum_eval_torus_mul_labelledRep`: for a finite label set `Λ`,
  `∑_α f (ϖ^lam * labelledRep ϖ σ α) = ∑_(|S| = i) |Λ|^(#radical pairs of S) * f (ϖ^(lam + 1_S))`.
  The index type is a sigma type over subsets, and the inner sum over labellings
  is constant, with `|Λ|^(#radical pairs)` terms (`Fintype.card_fun`).

## Vanishing away from dominant exponents

- `adjacentUnit_mem_integralSubgroup`: the elementary matrix `1 + x E_(i,i+1)`
  (published `Whittaker.UpperUnipotentCharacter.adjacentUnit`) lies in `K` for
  integral `x`; its inverse is `1 - x E_(i,i+1)`.
- `torus_inv_conj_adjacentUnit`: `t⁻¹ (1 + x E_(i,i+1)) t = 1 + ϖ^(-lam i) x ϖ^(lam (i+1)) E_(i,i+1)`.
- `eval_torus_eq_zero_of_not_antitone`: let `ϖ` be a uniformizing element, `f`
  equivariant and right `K`-invariant, and suppose that for every `i` there is `x`
  with `v x * v ϖ ≤ 1` (that is, `x ∈ ϖ⁻¹ O`) and `θ (1 + x E_(i,i+1)) ≠ 1`. Then
  `f (ϖ^lam) = 0` for every non-antitone `lam`. Proof: pick `i` with
  `lam i < lam (i+1)` (`Fin.antitone_iff_succ_le`) and such an `x`. The conjugate
  `k = t⁻¹ (1 + x E_(i,i+1)) t` has entry `ϖ^(lam (i+1) - lam i) x`, of valuation at most
  `v ϖ * v x ≤ 1`, so `k ∈ K`. Then
  `θ(1 + x E_(i,i+1)) f(t) = f((1 + x E_(i,i+1)) t) = f(t k) = f(t)`, and
  `θ(1 + x E_(i,i+1)) ≠ 1` forces `f(t) = 0`.

## Provenance

Internal (derived). These are the standard computations behind the Hecke
recursion for spherical Whittaker functions in Shintani, *On an explicit formula
for class-1 "Whittaker functions" on GL_n over p-adic fields* (1976), and
Casselman–Shalika (1980), written here for the published coset representatives.
