# The Haar modulus of torus conjugation on `N_m(𝔸)`

Module `Langlands.Global.RankinSelberg.UnipotentConjugationModulus`, namespace
`Langlands.Global.RankinSelbergGlobal.UnipotentConjugationModulus`.

## Content

A helper module for the proof of the one-place Iwasawa cell decomposition
`WhittakerCellDecompositionStatement`. The main result is
`mulEquivHaarChar_conj_localPoint_torus`: conjugation `n ↦ a n a⁻¹` by
`a = ι_v(ϖ^λ)` multiplies Haar measure on `N_m(𝔸)` by
`N(v) ^ (-∑_(i<j) (λ_i - λ_j))`. Here `ι_v(ϖ^λ)` is `localPoint F m v (torus ϖ λ)`, with
`ϖ^λ = diag(ϖ^λ_1, …, ϖ^λ_m)` at the finite place `v` and the identity elsewhere. `ϖ` is a
uniformizer of `F_v`, `N(v) = Ideal.absNorm v.asIdeal`, and `N_m(𝔸)` is the Library's
`unipotentAdelic F m`. The exponent is the statement module's `modulusExponent λ`.

### Ranked triangular coordinates

- `mulEquivHaarChar_eq_prod_of_rankTriangular`: let `H` be a locally compact group with
  Borel measurable structure, and `A` a locally compact, second-countable additive group
  with an additive Haar measure `ν`. Let `Φ : H ≃ₜ (I → A)` be coordinates indexed by a
  finite type `I` with a function `rank : I → ℕ`. Suppose that for every `g ∈ H` the
  difference `Φ(g Φ⁻¹(x))_k - x_k` depends only on the coordinates `x_l` with
  `rank l < rank k`. Let `ψ` be a continuous automorphism of `H` acting on the
  coordinates by `Φ(ψ h)_k = s_k(Φ(h)_k)`, where each `s_k` is measurable and
  `r_k · (s_k)_* ν = ν`. Then the Haar character of `ψ` is `∏_k r_k`.
  This restates the Library's `TriangularHaarModulus` for a general index type and rank.

### Conjugation and coordinates

`F` is a number field and `m` a natural number.

- `conjugation g : G ≃ₜ* G`: `x ↦ g x g⁻¹` in a topological group. `conjugation_apply`
  unfolds it.
- `prod_zpow_eq_zpow_sum`: `∏_(i∈s) g ^ e_i = g ^ ∑_(i∈s) e_i` in a commutative group.
- `UpperIndex m`: the strictly upper positions `(i, j)`, `i < j`, as the sigma type
  `Σ i, {j // i < j}`. `sum_upperIndex` rewrites a sum over it as
  `∑_i ∑_(j ∈ Ioi i)`.
- `matrixOf x`: the adelic matrix in `M_m(𝔸)` of a point `x ∈ GL_m(𝔸)`, through the
  Library's `GeneralLinearGroupPoints.adelicEquiv`. `matrixOf_mul`: it is multiplicative.
  `continuous_matrixOf`: it is continuous.
- `matrixOf_inv_of_diagonal`, `matrixOf_conj_apply`: if `matrixOf a = diag(d)` with
  `d_i ∈ 𝔸ˣ`, then `matrixOf a⁻¹ = diag(d⁻¹)` and
  `matrixOf(a x a⁻¹)_ij = d_i · matrixOf(x)_ij · d_j⁻¹`.
- `mem_unipotentAdelic_iff`: `x ∈ N_m(𝔸)` if and only if `matrixOf x` is unitriangular
  (the Library's `Unfolding.mem_unipotentAdelic_iff`).
- `conj_mem_of_diagonal`, `conj_mem_iff_of_diagonal`: a point with diagonal matrix
  normalizes `N_m(𝔸)`.
- `upperMatrix c`: the unitriangular matrix with strictly upper entries `c`.
  `isUnitriangular_upperMatrix` and `continuous_upperMatrix` record that it is
  unitriangular and continuous in `c`.
- `pointOf c`: the point of `GL_m(𝔸)` with matrix `upperMatrix c`. `matrixOf_pointOf`,
  `pointOf_mem` and `continuous_pointOf` give its matrix, its membership in `N_m(𝔸)`, and
  continuity.
- `coordinates F m : N_m(𝔸) ≃ₜ (UpperIndex m → 𝔸)`: **entry coordinates**, sending `n` to
  its strictly upper entries. `coordinates_apply` and `matrixOf_coordinates_symm` unfold
  it.
- `coordinates_mul_sub_eq`: left translations are triangular for the rank `m - i` of the
  entry `(i, j)`. For `g ∈ N_m(𝔸)`, the `(i, j)` entry of `g n` minus that of `n` depends
  only on the entries `(k, j)` of `n` with `k > i`.
- `coordinates_conj_of_diagonal`: if `matrixOf a = diag(d)`, then conjugation by `a`
  multiplies the coordinate `(i, j)` by `d_i d_j⁻¹`. The automorphism of `N_m(𝔸)` here is
  the Library's `QuotientIntegration.subgroupAutomorphism`, the restriction of
  `conjugation a`.

### The point `ι_v(ϖ^λ)`

- `coe_finiteIdeleInclusion`: the Library's idele `finiteIdeleInclusion F v u` is the pair
  `(1, finiteSingle F v u)` of `WhittakerCellAdelicScaling`.
- `matrixOf_localPoint_torus`: `matrixOf(ι_v(ϖ^λ))` is the diagonal matrix of the ideles
  `ι_v(ϖ^(λ_i))`.
- `conj_localPoint_torus_mem_iff`: `ι_v(ϖ^λ)` normalizes `N_m(𝔸)`.
- `mulEquivHaarChar_conj_localPoint_torus`: **the modulus of `ι_v(ϖ^λ)` on `N_m(𝔸)`.** If
  `ϖ` is uniformizing for `valuation F v`, then for every `λ ∈ ℤ^m` the Haar character of
  the restriction of `conjugation (ι_v(ϖ^λ))` to `N_m(𝔸)` is
  `N(v) ^ (-modulusExponent λ)`. The measurable-space structure and local compactness of
  `N_m(𝔸)` are hypotheses: `[MeasurableSpace _] [BorelSpace _] [LocallyCompactSpace _]`.
  The normalizing property is passed as an argument `hα`, which
  `conj_localPoint_torus_mem_iff` supplies.

## Proofs

`mulEquivHaarChar_eq_prod_of_rankTriangular`: let `π = ∏_k ν` and `μ = Φ⁻¹_* π`. Left
translation by `g` is, in coordinates, `x ↦ x + t(x)` with `t(x)_k = Φ(g Φ⁻¹ x)_k - x_k`
depending only on coordinates of smaller rank. The Library's
`HarmonicAnalysis.finiteTriangularTranslation` makes such a map preserve `π`, so `μ` is
left invariant. `μ` is finite on compacts and positive on open sets, being the image of
`π` under a homeomorphism. It is therefore a Haar measure, and it is regular because `H`
is second countable through `Φ` (`regular_of_isMulLeftInvariant`). In coordinates `ψ` is
the product map `∏ s_k`. Mathlib's `Measure.pi_map_pi` with
`(s_k)_* ν = r_k⁻¹ · ν` and the Library's `pi_nnreal_smul` give
`(∏ s_k)_* π = (∏ r_k)⁻¹ · π`. So `(∏ r_k) · ψ_* μ = μ`, and the Library's
`HarmonicAnalysis.mulEquivHaarChar_eq_of_smul_map` gives the character.

`coordinates`: the inverse map is `c ↦ pointOf c`. Both composites are the identity: the
entries of a unitriangular matrix below and on the diagonal are fixed, and the strictly
upper entries of `upperMatrix c` are `c`. Continuity holds in both directions: entries of
`matrixOf` are continuous, and `pointOf` is continuous because the inverse of a
unitriangular matrix is its adjugate (`Units.continuous_iff`).

`coordinates_mul_sub_eq`: the entry `(i, j)` of `g n - n` is
`∑_k (g - 1)_(i k) · n_(k j)`. Since `g` is unitriangular, `(g - 1)_(i k) = 0` unless
`k > i`. For `k > i`, the entry `n_(k j)` of `upperMatrix x` is either a coordinate
`x_(k, j)` of rank `m - k < m - i`, or a constant `0` or `1`.

`matrixOf_localPoint_torus`: `ι_v(ϖ^λ)` corresponds to
`AdelicGL.ofFinite (localInclusion v (ϖ^λ))`. Its infinite part is the identity, its
`v`-component is `ϖ^λ`, and its `w`-component for `w ≠ v` is the identity
(`FiniteAdelicGL.localProjection_localInclusion(_of_ne)`). Comparing entries at every
place gives the diagonal matrix of the ideles `ι_v(ϖ^(λ_i))`.

`mulEquivHaarChar_conj_localPoint_torus`: with `t = ι_v(ϖ)` and `d_i = t ^ λ_i`,
`matrixOf(ι_v(ϖ^λ)) = diag(d)`. Apply the ranked triangular lemma to the entry
coordinates, with `ν = addHaar` on `𝔸_F`, rank `m - i`, and `s_(i,j)` multiplication by
`c_(i,j) = d_i d_j⁻¹ = t ^ (λ_i - λ_j)`. Mathlib's `addEquivAddHaarChar_smul_map` gives
`r_(i,j) = mulLeftHaarChar(c_(i,j))`. Since `mulLeftHaarChar` is a homomorphism,
`∏ r_(i,j) = mulLeftHaarChar(t ^ ∑_(i<j)(λ_i - λ_j))`. This is
`N(v) ^ (-modulusExponent λ)` by `addEquivAddHaarChar_mulLeft_finiteIdeleInclusion_zpow`.

## Provenance

The formula is the modulus of the torus acting on the unipotent radical,
`δ_B(ϖ^λ) = ∏_(i<j) |ϖ^(λ_i - λ_j)|_v = q_v ^ (-∑_(i<j)(λ_i - λ_j))`. Cogdell (Fields
lectures 2003, Lecture 7 §3, p.57) uses it in the local formula
`dh = dn δ_B⁻¹(ϖ^J) dk`. The Lean proof is internal to this project. It computes in entry
coordinates on `N_m(𝔸)`, extends the Library's triangular Haar modulus lemma, and uses the
adelic scaling of `WhittakerCellAdelicScaling`.
