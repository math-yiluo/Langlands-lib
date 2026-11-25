# Localizations, chart lemmas on basic opens, and gluing

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. This module supplies
the localization bookkeeping and the gluing step of the Čech argument.

## Localizations and restriction

- `Loc c` is `Localization.Away c` for `c : C`.
- `isUnit_loc` and `isUnit_loc_of_dvd` record that `c`, and every divisor
  of `c`, becomes a unit in `Loc c`.
- `res c T h : Loc c →ₐ[C] T` is the `C`-algebra map to any `C`-algebra in
  which `c` is a unit (`IsLocalization.liftAlgHom`).
- `algHom_loc_ext` says that `C`-algebra maps out of `Loc c` are unique
  (`IsLocalization.algHom_subsingleton`).
- `restr ρ y = Spec.map ρ ≫ y` is restriction of a morphism along a
  `C`-algebra map. `restr_restr` says that restrictions compose.
- `rr h y` is restriction from `Spec (Loc c)` to `Spec (Loc c')` for
  `h : c ∣ c'`. `rr_rr` says it is independent of the path, since the
  algebra maps between localizations are unique.

## Chart representatives under restriction and combination

- `Chart.rep_restr_apply`, `Chart.rep_rr`: representatives restrict by
  applying the ring map.
- `Chart.rep_congr`: equal lifts have equal representatives.
- `Chart.eq_of_rep`: lifts with equal representatives are equal.
- `Chart.rep_comb_apply`: the representative of `Chart.comb` is the
  pointwise affine combination.
- `Chart.eq_comb_of_rep`: a lift whose representative is such a
  combination equals `Chart.comb`.
- `Chart.exists_lift`: lifts exist over a chart.
- `Chart.ψ_restr`: the chart representative of `s` is natural in the ring.

## Extension and torsion on basic opens

- `Chart.exists_extension_loc` applies `exists_extension` with `B = Γ(X, U)`
  over `A = Γ(S, V)`, `R = C[1/c]`, `R' = C[1/(c e)]`, `J = I R`, and
  `ρ = res`.
  - Finite presentation of `Γ(S, V) → Γ(X, U)` comes from smoothness.
  - The two localization hypotheses are `away_ker_torsion` and
    `away_map_surj`.
  - Given a lift `y` on `C[1/c]` and a lift `y'` on `C[1/(c e)]`, for all
    large `N` it produces a lift `z` on `C[1/c]` whose restriction has
    representative `y| + eᴺ (y' - y|)`.
- `Chart.exists_torsion_loc` applies `exists_pow_mul_sub_eq_zero`: two lifts
  on `C[1/c]` with equal restrictions to `C[1/(c e)]` have representatives
  differing by `e`-power torsion, uniformly.

## Gluing

- `glue_compat` and `exists_glue`: let `g : Fin n → C` generate the unit
  ideal, and let morphisms `yᵢ : Spec C[1/gᵢ] ⟶ X` agree on every
  `Spec C[1/(gᵢ gⱼ)]`. Then they glue to `z : Spec C ⟶ X` with
  `Spec.map (algebraMap C C[1/gᵢ]) ≫ z = yᵢ`.
  - The cover is `Scheme.affineOpenCoverOfSpanRangeEqTop`, and the morphism
    is `Scheme.Cover.glueMorphisms`.
  - Compatibility on the abstract pullback is checked on affine points with
    `Langlands.AlgebraicGeometry.AffinePoints.hom_ext`. An affine point
    `Spec A` of the pullback gives two maps `C[1/gᵢ] → A` and
    `C[1/gⱼ] → A`, agreeing on `C`. Both factor through `C[1/(gᵢ gⱼ)]`, by
    uniqueness of `C`-algebra maps out of localizations.
- `isLift_of_cover`: a morphism `z : Spec C ⟶ X` whose restrictions to the
  `Spec C[1/gᵢ]` are lifts solves the global problem. Both equations are
  checked on standard open covers (`Scheme.Cover.hom_ext`).
  - The equation `z ≫ f = s` is checked on the cover of `Spec C`.
  - The equation `Spec.map (mk I) ≫ z = x₀` is checked on the cover of
    `Spec (C ⧸ I)` by the images of the `gᵢ`. The comparison map
    `C[1/gᵢ] → (C ⧸ I)[1/gᵢ]` kills `I C[1/gᵢ]` and so factors through the
    reduction.

## Provenance

These are internal lemmas: standard localization and Zariski gluing,
written for this proof.
