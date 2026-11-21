# Conditional separation of points and tangents by the cube of an ample bundle

`Langlands.AbelianScheme.algClosedFieldAmpleCubeSeparation_of_generic` gives
`AlgClosedFieldAmpleCubeSeparationStatement.{u}` from
`AmpleGenericTranslationVanishingStatement.{u}` and
`AmpleGenericTangentVanishingStatement.{u}`. It does not prove the two premises.
This is the translate construction of Mumford, *Abelian Varieties*, §17
(printed pp.163–164, PDF pp.86–87 of `mumford-abelian-varieties-full-scan`),
adapted to use all sections of `L ⊗ L` in place of divisors of reduced sections
of `L`.

## Helpers

- `squareInvTranslate G c` is the group-scheme multiplication map `[-2]`
  followed by translation by `c`. `comp_squareInvTranslate` computes its effect
  on rational points using `GroupScheme.points_multiplication` and
  `comp_translation`. `isIso_translation_left` uses translation by the inverse
  point as inverse, and `surjective_squareInvTranslate` uses the published
  `multiplicationIsogeny` for `[-2]` and surjectivity of an isomorphism. This works
  even in characteristic two: the integer `-2` is nonzero, and no étaleness of
  multiplication by `-2` is claimed.
- `mem_preimage_trivializationOpen_iff` rewrites membership in the inverse image
  of the nonvanishing open of `s` by `f` as nonvanishing at the composite rational
  point. `preimage_trivializationOpen_nonempty` takes a preimage under the
  surjective underlying map of a point where `s` does not vanish.
- `cubeLBTensorPowIso` identifies the triple-translate construction's underlying
  module `(L ⊗ L) ⊗ L` with `tensorPow L.obj 3`, using tensor associativity and
  `tensorPowOneIso` for the last factor.

## Implemented proof

Fix `K`, `A`, and an ample `L` as in the separation statement. Use
`fieldTheoremOfTheSquare` to supply `SquareFor`, and
`exists_section_not_vanishesAlong_of_isAmple` to choose a section `s` of `L`
nonzero at some rational point. Set `N = squareLB G L` (`L ⊗ L`), ample by
`ampleTensor` and without rational base points by
`exists_squareSection_not_vanishesAlong`. The section constructions are from
`SquareSectionInvariance`. By `SeparatesPointsAndTangents.of_iso` and
`cubeLBTensorPowIso` it suffices to check the three clauses for `cubeLB G L`.

1. There is no rational base point by `exists_cubeSection_not_vanishesAlong`.
2. Suppose every cube section vanishing at `x₀` also vanishes at `x₁`. Put
   `x = x₀⁻¹ * x₁`; use the nonempty open inverse image of the nonvanishing open of
   `s` under `y ↦ x₀ * x₀ * x₁ * y⁻²`. At any rational `y` in this open take
   `a = y * x₀⁻¹`. Then `a * x₀ = y`, `a * x₁ = x * y`, and
   `s((a * a)⁻¹ * x₁) ≠ 0`. The lemma `vanishesAlong_square_of_not_separates`
   implies that a section of `N` through `y` also vanishes at `x * y`. The
   generic translation premise gives `x = 1`, contradicting `x₀ ≠ x₁`.
3. Suppose every cube section vanishing at `x₀` also vanishes on a nonzero tangent
   `t` there. Use the nonempty open inverse image under `y ↦ x₀ * x₀ * x₀ * y⁻²`
   instead. The vector at the unit is `t ≫ τ_{x₀⁻¹}`, nonzero by
   `isNonzeroTangentVectorAt_translate`. For rational `y` in this open use
   `a = y * x₀⁻¹` as before, so `s((a * a)⁻¹ * x₀) ≠ 0` and the translated
   vector at `y` is `t ≫ τ_a` by composition of translations. The lemma
   `vanishesAlong_square_translate_tangent_of_not_separates` gives precisely the
   condition excluded by the generic tangent premise.
