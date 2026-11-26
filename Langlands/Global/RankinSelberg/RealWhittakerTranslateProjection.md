# Compact averages of genuine right translates of real Whittaker coefficients

Module `Langlands.Global.RankinSelberg.RealWhittakerTranslateProjection`, namespace
`Langlands.Global.RankinSelbergGlobal`. This is the real-place counterpart of
`ComplexWhittakerCompactProjectionStatement` (module `ComplexLocalWhittakerGrowth`), and it has no
hypotheses beyond those displayed.

## Definitions

- `RealWhittakerTranslateProjection.IsRealCoefficientMap B`, for a complex-linear map
  `B` from the compact-finite real standard module `realStandardKFinite (r + 1) ds` to functions on
  `GL_(r+1)(ℝ)`, has three clauses. Every `B f` is smooth. If `f'` is the right translate of `f`
  by `k ∈ O(r+1)`, then `B f'` is the right translate of `B f` by `k`. If `f'` is the right
  derivative of `f` along a real matrix `X`, then `B f'` is the right derivative of `B f` along
  `X`. These are the second, fourth and fifth clauses of `IsRealWhittakerIntertwiner`, so
  `isRealCoefficientMap_of_intertwiner` gives the predicate for every real Whittaker
  intertwiner. The left character and growth clauses are not needed here. The inclusion of the
  standard module into functions satisfies it (`isRealCoefficientMap_subtype`).

## Statement

`RealWhittakerTranslateProjectionStatement r` takes the following data:

- a list `ds` of real blocks and a Haar measure `ν` on `O(r+1)` (`unitaryCompact ℝ (r+1)`);
- a continuous weight `κ` on `O(r+1)` whose left translates `k ↦ κ(h⁻¹ k)` span a
  finite-dimensional space;
- a map `B` with `IsRealCoefficientMap B`;
- a vector `f` of `realStandardKFinite (r + 1) ds` and `g ∈ GL_(r+1)(ℝ)`.

It asserts that some `p` in `realStandardKFinite (r + 1) ds` satisfies, for every
`x ∈ GL_(r+1)(ℝ)`,

`p(x) = ∫ κ(k) f(x k g) dν(k)` and `(B p)(x) = ∫ κ(k) (B f)(x k g) dν(k)`.

So the right translate by `g` need not be compact-finite, but its compact average with such a
weight is, and the average commutes with `B`. `realWhittakerTranslateProjection` proves the
statement.

## Proof

The proof follows the complex proof of `complexWhittakerCompactProjection`, with the real place
of `ℚ` in place of a complex place of `ℚ(i)`.

1. **Lifts.** For a number field `F` and a real place `v`, `projection` is the projection of the
   archimedean group `GL_(r+1)(F_∞)` to its factor at `v`, and `inclusion` inserts a matrix at `v`
   with identities elsewhere (`projection_inclusion`). `pullback` pulls a smooth function on
   `GL_(r+1)(ℝ)` back to a smooth function on `GL_(r+1)(F_∞)`. By the chain rule
   (`pullback_differential`), the right derivative of a pullback along an archimedean Lie
   direction is the pullback of the right derivative along its projection. For a map `B` with
   `IsRealCoefficientMap B`, `coefficients` pulls back all values of `B`.
   `coefficients_enveloping` and `coefficients_compact` transport the enveloping algebra action
   and the standard compact action to the real standard module. They use
   `realPlaceEnvelopingProjection` and the orthogonal factor `compactProjection`. These
   declarations follow the private construction of the module `RealWhittakerEvaluation`, here
   generalized from Whittaker intertwiners to `IsRealCoefficientMap`.
2. **Joint finiteness.** The real standard module has an infinitesimal character
   (`realStandardLie_hasInfinitesimalCharacter`). The projection of the enveloping center is
   central (`projection_mem_center`), so every pulled-back coefficient is finite under the center.
   Its compact orbit lies in the image of the finite orbit span of its source vector. Hence
   `coefficients_jointFinite` holds.
3. **The pair family.** `liftPair v B hB f` is the two-member family made of the pullback of `f`
   and the pullback of `B f`. Its range `Q` is stable under the compact and enveloping actions
   (`liftPair_compact`, `liftPair_enveloping`). Its members have finite compact orbits
   (`liftPair_compactFinite`) and are jointly finite.
4. **Finite rank of the average.** `placeCompactMap v` embeds `O(r+1)` at `v` in the standard
   compact subgroup, and `projection_placeCompactMap` recovers the orthogonal matrix. The
   average `averageLM` with weight `κ` maps `Q` into `Q`: the average of a member lies in the
   closed span of its finite compact orbit. Restricting the first coordinate to `O(r+1)` is
   injective on `Q`, because principal series vectors are determined by their restriction to
   `O(r+1)` (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`). On averaged members this
   restriction lies in the span of the finitely many functions `αⱼ` of a separated kernel
   `κ(x⁻¹ k) = ∑ⱼ αⱼ(x) βⱼ(k)` (`exists_separated_kernel`), using left invariance of `ν`.
   Hence the image of `Q` under averaging is finite-dimensional.
5. **Translation.** The Library theorem `ArchimedeanGL.SmoothFamily.averagedTranslate_mem`
   (module `ArchimedeanCompactAverageTranslation`) now puts the average of the simultaneous right
   translate of `liftPair v B hB f` by `inclusion v g` in `Q`. Its proof uses real analyticity of
   jointly finite functions. Write it as `liftPair v B hB p`. Evaluating both coordinates at
   `inclusion v x` gives the two formulas (`compact_projection_atPlace`).
6. `realWhittakerTranslateProjection` applies step 5 to the real place of `ℚ`.

## Provenance

This is an internal result. It transfers the complex argument of `ComplexLocalWhittakerGrowth` to
the real place. The analytic input is the Library's simultaneous orbit density and joint-finite
analyticity, through `ArchimedeanCompactAverageTranslation`. The result gives genuine right
translates of compact-finite coefficients by compact-finite approximation, as needed for the
real form of the last-row argument in H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§6.2, Propositions 6.1–6.2, author pp. 41–42.
