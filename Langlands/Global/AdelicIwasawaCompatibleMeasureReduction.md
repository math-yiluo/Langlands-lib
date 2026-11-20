# Iwasawa-compatible Haar measures from the Iwasawa integration formula

Module `Langlands.Global.AdelicIwasawaCompatibleMeasureReduction` proves
`Langlands.Global.IwasawaCompatibleMeasureExistenceStatement` from two
statements already in the Library:

- `Langlands.Global.AdelicGroupPoints.AdelicIwasawaIntegrationStatement.{0}`.
  For a dynamic parabolic `P(χ) = M U` and a compact `K` with
  `P(𝔸) K = G(𝔸)`, it gives a constant `c > 0` with
  `∫_G f dg = c ∫_K ∫_M ∫_U δ_P(m)⁻¹ f(u m k) du dm dk`, where `dg`, `dm`,
  `du` are Mathlib's Haar measures and `δ_P` is `parabolicModulus`.
- `Langlands.Global.AdelicGroupPoints.AdelicParabolicModulusStatement.{0}`.
  Only its second clause is used: Mathlib's modular character of `P(𝔸)` is
  `parabolicModulus`.

The module states the reduction as the proposition
`Langlands.Global.IwasawaCompatibleMeasureIntegrationReductionStatement`
(`AdelicIwasawaIntegrationStatement.{0} → AdelicParabolicModulusStatement.{0} →
IwasawaCompatibleMeasureExistenceStatement`). It proves the proposition as
`Langlands.Global.iwasawaCompatibleMeasureIntegrationReduction`.

Provenance. The target is Mœglin–Waldspurger I.1.13: some Haar measure on
`M(𝔸)` satisfies the Iwasawa integration formula when `du` gives
`U(F) \ U(𝔸)` volume one and `dk` is the probability Haar measure. The
reduction itself is internal. It only renormalizes the two measures in the
published integration formula: Mathlib's Haar measure on `U(𝔸)` becomes the
Library's `normalizedHaarMeasure` on `U(𝔸) ⊆ G(𝔸)`, and the weight
`δ_P(m)⁻¹` becomes `m^{-2ρ_P}` (`parameterPower F P (-modulusParameter F P)`).
Both renormalizations are needed because `IsIwasawaCompatibleMeasure` is
written in those terms.

## Declarations

Namespace `Langlands.Global.IwasawaCompatibleMeasure`:

- `exists_integral_adelicRangeMap_eq`. Let `j : U → G` be a closed
  immersion of affine group schemes of finite type over a number field `F`.
  Assume the quotient of the image `j(U(𝔸))` by its rational points is
  compact. Then some
  `β > 0` satisfies
  `∫_{U(𝔸)} g(j u) du = β ∫ g dν` for every `g : j(U(𝔸)) → ℂ`. Here `du`
  is Mathlib's Haar measure on `U(𝔸)` and `ν` is
  `AdelicSubgroupPoints.normalizedHaarMeasure F G (range j)`.
  Proof: `u ↦ j u` is a continuous surjection onto the closed subgroup
  `j(U(𝔸))` and a closed embedding (`isClosedEmbedding_map`). So the image
  of Mathlib's Haar measure under it is a Haar measure
  (`Measure.isHaarMeasure_map`), equal to `b • haar` with `b > 0`
  (`isMulLeftInvariant_eq_smul`, `haarScalarFactor_pos_of_isHaarMeasure`).
  By definition `ν = N • haar`, where `N = quotientMassNormalizer` is the
  reciprocal of the total mass of `rationalQuotientHaarMeasure` (the
  quotient Haar measure on the rational quotient of the image subgroup
  `range j`); it is finite and nonzero. Put `β = b / N`. Then
  `β • ν = b • haar`, which is the image of Mathlib's Haar measure on
  `U(𝔸)`, and `integral_map` turns the integral over `U(𝔸)` into `β`
  times the integral over the image for `ν`.
- `parameterPower_neg_modulusParameter`: for `q ∈ P(𝔸)`, the number
  `m^{-2ρ_P}` at `q` is `‖det Ad_P(q)‖⁻¹`. Here `‖det Ad_P(q)‖` is the
  idele norm `characterNorm F P (Lie.adjointDeterminantCharacter P)`. The
  proof unfolds `parameterPower`, `modulusParameter` and `characterLog`,
  which gives `exp(-log ‖det Ad_P(q)‖)`.
- `parabolicModulus_eq_characterNorm`: under
  `AdelicParabolicModulusStatement`, `δ_P(q) = ‖det Ad_P(q)‖` on `P(𝔸)` for
  a dynamic parabolic `P(χ)` of a connected reductive `G`. The second clause
  of the premise, for the coordinates `Lie.finiteCoordinates U`, says the
  modular character of `P(𝔸)` is `δ_P`. The published
  `PlaceGroupPoints.localModularCharacterAdjointDeterminant` and
  `modularCharacter_eq_characterNorm_of_local` say this modular character is
  `‖det Ad_P‖`; these need `P` smooth, which `dynamicSmooth` gives.
- `iwasawaCompatibleMeasureExistence_of_integration`: the target from the
  two premises. Take `F`, `G`, `P`, `M`, `U`, `K` as in the target, with the
  root presentation `r` and geometric unipotent radical `iU`. The cocharacter
  `χ = a ∘ r.splitComponentCocharacter` (pushed into `G` through `l` and `p`)
  has dynamic parabolic, centralizer and unipotent radical represented by `p`,
  `l ≫ p` and `iU ≫ p`. These are `r.parabolic_eq_splitComponentCocharacter`,
  `r.levi_eq_splitComponentCocharacter` and `r.range_comp_radical_eq`. The
  integration premise for these data and `K` (compact, `P(𝔸) K = G(𝔸)` from
  `IsIwasawaCompact`) gives `c > 0`. Since `U` is smooth, connected and
  unipotent, `U(F) \ U(𝔸)` is compact
  (`compactSpace_rationalQuotient_range_unipotent`), so
  `exists_integral_adelicRangeMap_eq` gives `β > 0`. The measure is
  `μ_M = (c β) • haar`, a Haar measure since `c β > 0`. For each `k` and `m`,
  the inner integral of the target over `ν` is `β⁻¹` times the inner
  integral of the premise over `U(𝔸)`. This uses three pointwise facts:
  `centralizerToParabolic` agrees with `l` on `M(𝔸)` (both composites with
  the injective `p` agree); the two lemmas above turn `m^{-2ρ_P}` into
  `δ_P(m)⁻¹`; and `j u` is `map F U G (iU ≫ p) u` (`rfl`). Integrating over
  `μ_M` and then over `K` gives `(c β) β⁻¹ = c` times the premise's triple
  integral, which is `∫_G f`.

Namespace `Langlands.Global`:

- `IwasawaCompatibleMeasureIntegrationReductionStatement` (the proposition
  above) and `iwasawaCompatibleMeasureIntegrationReduction`, its proof by
  `iwasawaCompatibleMeasureExistence_of_integration`.

The maximal-compactness hypothesis `IsMaximalCompactSubgroup F G K` of the
target is not used.
