# `c_M` of a family of Schwartz functions (Lapid's Corollary 3)

Module `Langlands.LinearAlgebra.GMFamilySchwartzExtension` proves that for a
`(G, M)`-family `{d_P}` of Schwartz functions on `StrongDual ℝ a` (the points
`λ = iΛ` of `i𝔞_M^*`), the function `d_M = ∑_P d_P θ_P⁻¹` extends to a Schwartz
function whose seminorms are controlled by those of the `d_P`: for each fixed
output order `K` there are an order `K'` and a constant `C`, depending only on
the root set, the Levi space and `K`, with
`schwartzSup K (d_M) ≤ C · ∑_P schwartzSup K' (d_P)`. The module claims no
bound with `K'` and `C` independent of `K`.

## Results

- `schwartzSup 𝕜 K`: the supremum of the Schwartz seminorms of orders
  `(k, n) ≤ (K, K)`; `seminorm_le_schwartzSup`, `schwartzSup_mono`, and
  `schwartzSup_real_eq` (its value does not depend on the scalar field).
- `exists_schwartzSup_bound`, `exists_schwartzSup_bound_schwartz`: a continuous
  linear map into a Schwartz space is bounded, for each `K`, by a constant
  times a finite supremum of the seminorms of its domain
  (`Seminorm.bound_of_continuous`).
- `exists_division_bound`: the seminorm bound for
  `Langlands.Analysis.schwartzLinearDivision`, the division of a Schwartz
  function vanishing on the kernel of a nonzero linear form `ℓ` by `ℓ`
  (Lapid's Lemma 7, from the Library module
  `Langlands.Analysis.SchwartzLinearDivision`).
- `exists_iterated_division`: let `ℓ_j ≠ 0` for `j ∈ s` and fix an order
  `K`. Then there are `K'` and `C ≥ 0`, depending on the forms and on `K`,
  such that whenever `g` is a Schwartz function and
  `g = (∏_{j ∈ s} i ℓ_j) · h` with `h` continuous, `h` is a Schwartz function
  and `schwartzSup K h ≤ C · schwartzSup K' g`. (For `s = ∅` the proof takes
  `K' = K` and `C = 1`.) Induction on `s`; in the step for
  the index set `insert i s` (with `i ∉ s`) one has
  `g = (∏_{j ∈ insert i s} i ℓ_j) · h`, so `g` vanishes on `ker ℓ_i`, and the
  quotient `−i · g/ℓ_i` (from `schwartzLinearDivision`) equals
  `(∏_{j ∈ s} i ℓ_j) · h`, the product over the remaining indices, on the
  dense set `ℓ_i ≠ 0` (`dense_nonzero_forms`), hence everywhere by
  continuity; the induction hypothesis for `s` applies to this quotient.
- `hasTemperateGrowth_finset_prod`, `hasTemperateGrowth_imaginaryEval`,
  `theta_hasTemperateGrowth`: `θ_S` and products of such factors have
  temperate growth, so multiplication by them is a continuous linear map of
  the Schwartz space (`SchwartzMap.smulLeftCLM`).
- `exists_schwartz_cM` (Lapid's Corollary 3, with bounds): for every fixed
  output order `K` there are `K'` and `C ≥ 0`, depending on `R`, `a` and `K`,
  such that for every `(G, M)`-family `d` of Schwartz
  functions there is a Schwartz function `F` with `F = cM R a d` wherever all
  `θ_S ≠ 0`, and
  `schwartzSup K F ≤ C · ∑_S schwartzSup K' (d S)`.

## Proof of `exists_schwartz_cM`

Let `Θ = ∏_S θ_S`, which is a nonzero constant `C₀` times the product of the
imaginary linear factors `i Λ(v)` over all pairs `(S, v)`, `v ∈ simpleRoots a S`
(the Gram volumes of the simple roots are nonzero by `gramVolume_pos_iff`).
Put `N = ∑_S π_S · d_S` with `π_S = ∏_{S' ≠ S} θ_{S'}`; it is a Schwartz
function, and its seminorms are bounded by those of the `d_S` since
multiplication by `π_S` is continuous. The Library's smooth extension
`smoothExtension` (Arthur's Lemma 17.1) gives a smooth `F₀` equal to `c_M` off
the walls; there `N = Θ · c_M = (∏ i ℓ_σ) · (C₀ F₀)`, and both sides are
continuous, so the identity holds everywhere. The forms `ℓ_σ : Λ ↦ Λ(v)` are
nonzero because the simple roots `v` are nonzero vectors of `a`, so
`exists_iterated_division` applies and shows that `C₀ F₀` is a Schwartz function with bounded seminorms, and
`F = C₀⁻¹ · (C₀ F₀)`.

## Provenance

E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein
series*, Clay Math. Proc. 13 (2011), §7, Lemma 7 and Corollary 3, pp. 325–326
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`).
Lapid states the continuity of `{d_P} ↦ d_M` on Schwartz spaces; this module
proves it in the explicit form of seminorm bounds, by the same division
argument applied to the common numerator.
