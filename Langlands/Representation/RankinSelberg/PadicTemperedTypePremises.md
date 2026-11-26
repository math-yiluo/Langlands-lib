# The premises of the specialized (9.4) argument over p-adic fields

Module `Langlands.Representation.RankinSelberg.PadicTemperedTypePremises`, namespace
`Langlands.RankinSelberg.PadicTemperedType`. For a p-adic field `K : PadicField p`, the
field `K.Carrier` carries the canonical topology, valuation and local-field structure of
`K.canonicalTopologicalData` (file-local instances). At these structures the all-field
constructions of `LocalFieldData.ofInstances K.Carrier` (normalized induction, determinant
norms, self-dual Haar measures, L-polynomial relations) are definitionally those of the
Library's p-adic development, so the premises follow directly from p-adic theorems.

## Contents

- `inducedTailLFactorAt K : AllField.RankinSelberg.InducedTailLFactorAt K.Carrier`: JPSS
  1983, Lemma (9.3), from the published `inducedTailLFactor`.
- `isTemperedRepresentation_iff`: `IsTemperedRepresentation` is
  `K.canonicalTopologicalData.IsTempered` (`Iff.rfl`).
- `temperedPoleBound K : AllField.RankinSelberg.TemperedPoleBoundStatement K.Carrier`: JPSS
  1983, (8.4), from the published `analyticTemperedTwistLPolynomial_poleFree` at the
  exponents `0` (published `realPowerTwist_zero`).
- `temperedRankWhittaker`: irreducible tempered representations of positive rank are of
  Whittaker type for every `ψ` (published `analyticTemperedWhittakerType`).
- `temperedTypeDatumOf K t`: the tempered-type datum of a tempered Langlands datum `t`
  (`PadicField.TopologicalData.TemperedLanglandsDatum`); its exponents are strictly, hence
  weakly, decreasing. `temperedTypeDatumOf_standardModule`: the standard modules agree
  (`rfl`).
- `genericStandardModule K :
  AllField.RankinSelberg.GenericStandardModuleStatement K.Carrier`. For `π` generic, its
  lift to the carrier universe `max uF uV` is a Langlands quotient of the standard module
  of some tempered Langlands datum `t` (published
  `Classification.temperedLanglandsQuotientCoverage`). The standard module is of Whittaker
  type and has the Whittaker functions of `π` for `ψ` and for `ψ⁻¹`, by the published
  lemmas `standardModule_isOfWhittakerType_of_surjective`,
  `whittakerSet_eq_of_surjective_of_whittakerType` and
  `inverseWhittakerSet_eq_of_surjective_of_whittakerType` (module
  `GenericLanglandsQuotientLFactorProof`) applied to the surjection onto `π`.

Source: JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), (8.4), (9.3) and (9.4),
printed pages 451–462; the Library's p-adic results named above.
