# The universal scaled branch of a plane curve

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`.

Provenance. Schmidt (*Zur Methode von Stepanov*, Acta Arith. 24, 1973) controls the vanishing
of the auxiliary polynomial along the curve `f = 0` with hyperderivatives along the curve, which
are polynomials divided by powers of `f_Y`. This module replaces that device by a power-series
parametrisation of the curve, constructed once over `F[X][Y]` (the "universal branch") and later
specialised at points
(`PointBranch.lean`). The coefficient of `S^l` of `sigma P B` below plays the role of Schmidt's
derivatives along the curve, cleared of denominators: it is a polynomial with explicit degree
bounds. The construction is an own route, not a result of the literature.

Bivariate polynomials are `R2 = F[X][Y]` (outer variable `Y`), `F` a commutative ring.

## Definitions

- `InW α β a b Φ` for `Φ ∈ R2⟦S⟧`: for every `l`, the coefficient of `S^l` lies in the box
  `(a + l α, b + l β)` of `Box.lean`. Lemmas `inW_zero`, `InW.add/neg/sub/mono/mul/pow`,
  `inW_sum`, `inW_C`, `inW_X` (`S` has weight `(-α, -β)`).
- `tc P e₀ e₁`: the coefficient of `U^e₀ V^e₁` in `P(X + U, Y + V)` (`Taylor.lean`);
  `tc_zero_zero` (`= P`), `tc_zero_one` (`= derivative P`), `inBox_tc` (box `(a - e₀, b - e₁)`).
- `subst c Z : R2 →+* R2⟦S⟧`: the substitution `X ↦ X + c² S`, `Y ↦ Y + c Z`; `evUV` evaluates
  `U = c² S`, `V = c Z`, and `evUV_comp_theta` shows `subst c Z = evUV c Z ∘ theta`.
- `bterm c t e₀ e₁ Z = C(t c^(2e₀+e₁-2)) S^e₀ Z^e₁` if `2e₀ + e₁ ≥ 2`, else `0`, and the
  fixed-point map `branchMap P c Z = -∑ bterm c (tc P e₀ e₁) e₀ e₁ Z` over the support of the
  Taylor expansion.
- `chiSeq P c k = (branchMap P c)^[k] 0` and the limit `chi P c`, whose coefficient of `S^l` is
  that of `chiSeq P c (l + 1)`.
- `sigma P = subst (derivative P) (chi P (derivative P))`, i.e.
  `B ↦ B(X + P_Y² S, Y + P_Y χ)`.

## Main results

- `subst_eq`: `subst c Z P = C P + C(P_Y · c) · Z - C(c²) · branchMap P c Z`; with `c = P_Y`
  this reads `subst c Z P = C P + C(c²)(Z - branchMap P c Z)`. Proved by expanding through
  `evUV_comp_theta` and `term_identity`.
- Contraction: if `S ∣ Z₁`, `S ∣ Z₂` and `S^k ∣ Z₁ - Z₂` then
  `S^(k+1) ∣ branchMap P c Z₁ - branchMap P c Z₂` (`bterm_sub_dvd`, via `geom_sum₂_mul`;
  `branchMap_sub_dvd`), and `branchMap` preserves `S ∣ Z` (`branchMap_dvd`). Hence
  `S^k ∣ chi - chiSeq k` (`chi_sub_dvd`), `S ∣ chi` (`chi_dvd`) and
  `branchMap_chi : branchMap P c (chi P c) = chi P c`.
- `subst_chi_self` / `sigma_self`: `sigma P P = C P`, i.e. `P(X + P_Y² S, Y + P_Y χ) = P`.
- Degree bounds: `inBox_derivative` (`P_Y` lies in box `(m, n - 1)` if `P` lies in `(m, n)`);
  `inW_bterm`, `inW_branchMap`, `inW_chiSeq`, and
  `inW_chi : InW (2m - 1) (2n - 2) (-m) (2 - n) (chi P c)`.
- `inW_sigma`: if `P` lies in box `(m, n)` and `B` in box `(a, b)`, then
  `InW (2m - 1) (2n - 2) a b (sigma P B)`: the coefficient of `S^l` of `sigma P B` lies in
  the box `(a + l(2m - 1), b + l(2n - 2))`. Proved with `map_fil_of_inBox` (`Taylor.lean`)
  for the filtration `InW`.
