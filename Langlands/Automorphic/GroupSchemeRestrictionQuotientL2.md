# Square-integrable classes on the restriction split-centre quotient

Author: Worker 112.

The published module `GroupSchemeQuotientL2` defines `L²` classes and the right
regular representation on the positive-torus quotient
`PositiveRealTorus.PositiveRationalQuotient F G T i`. That quotient uses the
positive image of an `F`-split central torus `i : T.toGrp ⟶ G`. Getz--Hahn
(2.20)--(2.21) (`getz-hahn-2024-automorphic-representations`, printed
pp. 68--69) instead form `[G] = A_G G(F) \ G(A_F)` with `A_G` taken from the
restriction of scalars. The published module `AdelicRestrictionSplitCentre`
builds that shape as `RestrictionSplitCentre.Quotient F G S j`, for a supplied
`j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`.

The published module `AdelicRestrictionSplitCentreQuotient` gives this
quotient the measure `quotientHaarMeasure F G S j`. Assuming
`h : subgroup F G S j = imageSubgroup F T G i`, it identifies the two quotients
by the identity on representatives, preserving the measures; this is
`quotientMeasurableEquiv F G h`. The present module carries the `L²`
construction over to the restriction quotient along that identification.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and `j` maps it into the Weil
  restriction.
- `T` is a commutative group scheme over `F` and `i : T.toGrp ⟶ G`.

The comparison hypothesis `h` is the conclusion of the published
`RestrictionSplitCentre.ComparisonStatement` for split components `j` and
`i`. Most results take `h` as a hypothesis. The last section discharges it
for split components with the published theorem
`RestrictionSplitCentre.comparison` from
`AdelicRestrictionSplitCentreComparison`.

## The L² identification

Assume `h`. Write `ν⁺ = positiveRationalQuotientHaarMeasure F G T i`,
`ν = quotientHaarMeasure F G S j` and `E = quotientMeasurableEquiv F G h`.
- `compMeasurePreserving_congr`: Mathlib's composition on `L²` depends only
  on the underlying function, not on the proof of measure preservation.
- `quotientL2Map F G h` is composition with `E.symm`, a linear isometry from
  `QuotientL2 F G T i ν⁺` to `Lp ℂ 2 ν`.
- `quotientL2InvMap F G h` is composition with `E`, a linear isometry in the
  other direction.
- `quotientL2InvMap_quotientL2Map` and `quotientL2Map_quotientL2InvMap`
  prove that the two are mutually inverse. Each composite is composition
  with `E.symm ∘ E` or `E ∘ E.symm`, both of which are the identity.
- `quotientL2Equiv F G h` is the resulting linear isometric equivalence,
  `QuotientL2 F G T i ν⁺ ≃ₗᵢ[ℂ] Lp ℂ 2 ν`.
- `coeFn_quotientL2Equiv` and `coeFn_quotientL2Equiv_symm` give the
  almost-everywhere formulas `f ∘ E.symm` and `f ∘ E`.

## Right invariance and full support

`QuotientRightInvariant F G measureQ` is the property that every actual
right translation `[x] ↦ [x * g]` of `Quotient F G S j` preserves `measureQ`.
It is the analogue of the published `QuotientMeasureRightInvariant`.
- `quotientRightInvariant_of_positive` proves that if `ν⁺` is right invariant
  in the published sense, then `ν` is right invariant. Right translation on
  the restriction quotient is `E ∘ R⁺(g) ∘ E.symm`, by the published
  `quotientHomeomorph_rightTranslate`.

The next two results take these hypotheses:
- `characterRestrict i` is injective and has finite-index range;
- `hc : IsCentral i` and `hT : IsSplitTorus T.toGrp`;
- Haar measure on `normOneSubgroup F G` is right invariant.

- `quotientHaarMeasure_rightInvariant` gives right invariance of `ν`. It
  extracts finite splitting coordinates from `hT` and applies the published
  `haarQuotientMeasureRightInvariant`.
- `quotientHaarMeasure_isOpenPosMeasure` proves that `ν` is positive on
  nonempty open sets. The norm-one quotient measure is positive on nonempty
  open sets by its published compatibility. The measure `ν` is its image
  under the homeomorphism `normOneQuotientHomeomorph` (Getz--Hahn (2.22)),
  whose underlying map is `normOneToQuotient`. The proof uses the Borel
  structure from `quotient_borelSpace`.

## Right regular representation

For any measure `measureQ` on `Quotient F G S j` with
`hInv : QuotientRightInvariant F G measureQ`:
- `rationalQuotientL2RightTranslate F G measureQ hInv g` is composition with
  right translation by `g`, a linear isometry of `Lp ℂ 2 measureQ`.
  `coeFn_rationalQuotientL2RightTranslate` gives its almost-everywhere
  formula `q ↦ f (q · g)`.
- `rationalQuotientL2RightTranslate_one` and
  `rationalQuotientL2RightTranslate_mul` give the identity and
  multiplication laws.
- `rationalQuotientL2RightAction F G measureQ hInv` is the resulting complex
  representation of the adelic points on `Lp ℂ 2 measureQ`.

`quotientL2Equiv_rightAction` proves that `quotientL2Equiv F G h` intertwines
the published `quotientL2RightAction` on the positive-torus quotient with
`rationalQuotientL2RightAction` on the restriction quotient. Both
right-invariance proofs are arbitrary hypotheses, and the proof reduces to the
identity `R⁺(g) ∘ E.symm = E.symm ∘ R(g)` of quotient maps.

## Split components

Assume `hj : IsSplitComponent j` and `hs : IsSplitComponent i`.
- `subgroup_eq_of_splitComponents F G hj hs` is the equality
  `subgroup F G S j = imageSubgroup F T G i`. It applies the published
  `subgroup_eq_of_comparison` to the published proof `comparison` of
  `ComparisonStatement`.
- `splitComponentL2Equiv F G hj hs` is `quotientL2Equiv` for this equality.

The next results also assume that `characterRestrict i` is injective with
finite-index range and that Haar measure on `normOneSubgroup F G` is right
invariant. Centrality and the split-torus property of `T` come from `hs`.
- `quotientHaarMeasure_rightInvariant_of_splitComponents` and
  `quotientHaarMeasure_isOpenPosMeasure_of_splitComponents` give right
  invariance of `ν` and positivity on nonempty open sets.
- `splitComponentL2RightAction F G hi hj hs` is
  `rationalQuotientL2RightAction` for `ν` with this right invariance.
- `splitComponentL2Equiv_rightAction` proves that `splitComponentL2Equiv`
  intertwines the published `quotientL2RightAction`, for any right-invariance
  proof of `ν⁺`, with `splitComponentL2RightAction`. It is
  `quotientL2Equiv_rightAction` for these data.

## Technical note

Three proofs use `set_option maxRecDepth 20000`: the two group laws and
`quotientL2Equiv_rightAction`. Unfolding the isometry coercions on these large adelic
types exceeds the default recursion depth.

## Provenance and scope

The quotient follows Getz--Hahn (2.20)--(2.22). Every construction here is
internal. It transports the published `L²` construction along the published
measure-preserving identification, using Mathlib's composition of `L^p`
classes with measure-preserving maps.

This module does not prove `ComparisonStatement`; it imports the published
proof. It does not prove the existence of split components, the injectivity
or finite index of `characterRestrict i`, unimodularity, finite volume, or any
spectral property. It does not construct cusp forms or constant terms on the
restriction quotient.
