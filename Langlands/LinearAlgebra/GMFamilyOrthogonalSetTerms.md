# The terms of the alternate splitting formula along a positive orthogonal set

Module `Langlands.LinearAlgebra.GMFamilyOrthogonalSetTerms` provides the
estimates for the integrals over `V = 𝔞_M^G` of the products
`c_M^{Q₁}(λ) d_M^{Q₂}(λ)` that occur when the alternate splitting formula is
applied to the product of the exponential family `c_P(λ) = e^{λ(Y_P)}` of a
positive `(G, M)`-orthogonal set and a `(G, M)`-family `d` of Schwartz
functions.

## The `d`-side

- `dualParamCLM`, `dualParamCLM_apply`, `norm_le_dualParamCLM`: the map
  `x ↦ Λ_x` as a continuous linear map `V → StrongDual ℝ a` with
  `‖x‖ ≤ ‖Λ_x‖`, so composition with it maps Schwartz functions to Schwartz
  functions (`SchwartzMap.compCLM`).
- `exists_face_schwartz`: for a face `Q₂ = posSet R w` and `N ∈ ℕ` there are
  `K`, `C` such that for every `(G, M)`-family `d` of Schwartz functions there
  is a Schwartz function `u` on `V` with `u(x) = d_M^{Q₂}(Λ_x)` off the walls
  and `(1 + ‖H‖)^N |phaseFourier u H| ≤ C ∑_P schwartzSup K (d_P)`. Here
  `d_M^{Q₂} = cQM R a d Q₂` is `c_M` of the restricted family
  `S ↦ d(Q₂ ∪ S)` for the roots of `M_{Q₂}` (`isFamily_face`); its Schwartz
  extension comes from `exists_schwartz_cM` (Lapid's Corollary 3), and the
  decay from `exists_phaseFourier_decay`. The function `phaseFourier u` is
  Lapid's `φ_{Q₂}` for the measure `dx`.

## Orthant integrals

Fix a chamber `P`, an injection `j : ι → Δ_P` and its basis
`chamberBasis` of `V`.

- `exists_chamber_coord_norm`: the coordinates in `chamberBasis` are bounded
  by a multiple of the norm.
- `chamberBasis_repr_orthant`: the `β`-coordinate of `Y − ∑_i X_i v_{j(i)}`
  is that of `Y` minus the sum of the `X_i` with `j(i) = β`.
- `one_add_pow_inv_le`: for `c > 0` and `t ≥ 0`,
  `(1 + ct)^{−n} ≤ max(1, c⁻¹)^n (1 + t)^{−n}`.
- `exists_orthant_term_bound`: there is `C` such that for `Y ∈ V` with
  `⟪v, Y⟫ ≥ t ≥ 0` for all `v ∈ Δ_P`, every `u` and `A ≥ 0` with
  `(1 + ‖H‖)^{n+|ι|+1} |phaseFourier u H| ≤ A`, and every measurable set `D`
  of coordinate vectors `X` each having some simple root `β` of `P` with
  `X_i ≤ 0` whenever `j(i) = β`,
  `|∫_D phaseFourier u (Y − ∑_i X_i v_{j(i)}) dX| ≤ C A (1 + t)^{−n}`.
  Write `y_β = (chamberBasis.repr Y)(β)` for the coordinates of `Y` in the
  basis `chamberBasis`, a function of `β ∈ Δ_P`, and `y ∘ j : ι → ℝ` for
  `i ↦ y_{j(i)}`. For such `X` the point `Z = Y − ∑ X_i v_{j(i)}` has
  `β`-coordinate at least `y_β`, which is `≥ c t` by
  `exists_chamber_coord_lower`, and its `j(i)`-coordinate is
  `y_{j(i)} − X_i` (`j` being injective); hence
  `‖Z‖ ≳ max(ct, ‖X − y ∘ j‖)` and `exists_integral_decay_bound` applies.
- `integrable_orthant_phaseFourier`: for a Schwartz `u` with
  `(1 + ‖H‖)^{|ι|+1} |phaseFourier u H| ≤ A`, the integrands
  `X ↦ phaseFourier u (Y − ∑_i X_i v_{j(i)})` are integrable on all of
  `ℝ^ι`.

## The formula

- `apply_simpleRoot_ne_zero_of_offWalls`: off the walls `Λ(v) ≠ 0` for the
  simple roots `v` of the chambers of a root subset `R' ⊆ R`.
- `inner_relative_projection`: `⟪x, pr_V h⟫ = ⟪x, h⟫` for `x ∈ V`.
- `integral_cM_exp_eq_orthants`: for a root subset `R' ⊆ R` with Levi space
  `a` whose chambers have simple roots among those of chambers of `R`, points
  `y_S` giving a family of exponentials, a point `ξ ∈ V` off the walls and a
  Schwartz test `u` with `phaseFourier u` decaying like
  `(1 + ‖H‖)^{−(dim V + 1)}`,

  `∫_V c_M(Λ_x) u(x) dx = ∑_S gram(S) · orthantSign(−Λ_ξ|_{Δ_S}) ·
     ∫_{orthant} phaseFourier u (pr_V(y_S − ∑_{v ∈ Δ_S} X_v v)) dX`,

  the orthant being `{−Λ_ξ(v) X_v > 0}`. This is `integral_cM_exp_mul` of
  `GMFamilyConeIntegrals` with `Ω = V` and `L = dualParam`, the shift being
  `μ = Λ_ξ`; the inner integral over `V` is `phaseFourier u` at the projected
  point.

## Provenance

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), §7, proof of Lemma 8,
pp. 326–327 (`lapid-2011-asymptotic-inner-product-truncated-eisenstein`,
volume PDF SHA-256
`760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`): Lapid
writes `∫ c_M^{Q₁}(T; λ) d_M^{Q₂}(λ) dλ` as the integral of `φ_{Q₂}` over the
convex hull of the projected points `Y_Q(T)` and bounds it using (15). Here
the convex hull is replaced by the signed orthants of the formula above. The
decay estimate applies to two kinds of regions (see
`GMFamilyOrthogonalSetBounds`):

- for a proper face (`Q₁ ≠ ∅`), every orthant of the formula: some
  simple-root coordinate of the projected point `pr_V(y_S − ∑ X_v v)` is not
  moved, so this point stays at distance `≳ t` from the origin;
- for the full family, the remainder regions only: the complement of the
  positive orthant in the chamber `P₀` of `−ξ`, and the orthants of the other
  chambers. On these some coordinate `X_v` is `≤ 0`, and the projected point
  stays at distance `≳ t`.

The positive orthant of `P₀` itself gives no decay. Since the simple roots
`v ∈ Δ_{P₀}` lie in `V`, the argument of `phaseFourier u` is the projected
point `pr_V(Y_{P₀}) − ∑ X_v v`; it vanishes when the `X_v` are the
`chamberBasis` coordinates of `pr_V(Y_{P₀})`. These coordinates are at least
`c t` (`exists_chamber_coord_lower`), so this zero lies inside the positive
orthant for `t > 0` and in its closure for `t ≥ 0`. (The unprojected point
`Y_{P₀} − ∑ X_v v` need not approach the origin, since `Y_{P₀}` may have a
component in `𝔞_G`.) The contribution of this orthant is written as the
integral over the whole coordinate space, which is
`gram(P₀)⁻¹ ∫_V phaseFourier u = gram(P₀)⁻¹ (2π)^{dim V} u(0)` by Fourier
inversion, minus the integral over the complementary region, which is one of
the remainder regions above. This is the counterpart of Lapid's (17).
