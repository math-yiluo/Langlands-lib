# Gamma assembly for two block families of Whittaker type, every local field

Module `Langlands.AllField.Representation.RankinSelberg.TemperedLFactorGamma`.

This module is the all-field port of the field-dependent part of the Library module
`Langlands.Representation.RankinSelberg.TemperedLFactorGamma`, together with the
all-field form of `Langlands.RankinSelberg.symmetricGammaExpression` (module
`Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof`). The field `F`
is any field with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`; the canonical data of a p-adic field are replaced by
`(⟨⟩ : LocalFieldData F)` and the reflection unit by
`Langlands.AllField.LocalFactor.residueReflection F` (`q⁻¹`). The field-free declarations
of the original (`TemperedLFactorGamma.ReflectedRatioData`,
`reflectedRatio_of_gammaExpression_eq`, `rationalGammaExpression_prod`) are used
unchanged.

## Contents

Namespace `Langlands.AllField.RankinSelberg`:

- `isPadicSymmetricEpsilonFactor_of_lt`: in the smaller-rank-first order, the symmetric
  epsilon relation is the pair relation of the exchanged pair.
- `symmetricGammaExpression`: under the construction input
  `PadicSymmetricGammaConstructionInput F ψ ν π σ`, a rational function is the symmetric
  gamma factor of `(π, σ)` exactly when it equals the canonical expression
  `rationalGammaExpression (residueReflection F) e.1 e.2 P Pdual` of any certified epsilon
  data `e` and L-polynomials `P` of `(π, σ)` and `Pdual` of the inverse-transpose pair for
  `ψ⁻¹`. The proof is that of the original, with the published all-field
  `IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput`.

Namespace `Langlands.AllField.RankinSelberg.TemperedLFactorGamma`:

- `epsilon_exists_of_whittakerType`: pairs of Whittaker type have certified epsilon data,
  extracted from the published all-field `whittakerTypeGammaConstructionInput`.
- `symmetricGammaFactor_swap`: exchange of the members of a pair of Whittaker type
  (published all-field `isPadicPairGammaFactor_swap_equalRank` in equal rank).
- `gamma_doubleProduct`: gamma multiplicativity (JPSS 1983, Theorem (3.1), printed pages
  404–405) in both block
  families (published all-field `gammaMultiplicativity`): the gamma factor of the two
  normalized products is the double product of the block gamma factors.
- `nonempty_reflectedRatioData`: for certified polynomials `P` of the two products, `Q i j`
  of the block pairs, `PD` of the inverse-transpose pullbacks of the products for `ψ⁻¹`
  and `QD i j` of the block pullbacks, the identity
  `B / B^ι(q⁻¹/X) = c X^m · P / P^ι(q⁻¹/X)` holds with `B = ∏ Q i j`, `B^ι = ∏ QD i j`,
  for a unit `c` and an integer `m`. It follows by writing every gamma factor as its
  canonical expression and comparing the double product with the product gamma factor.

Source: JPSS 1983 (literature ID `jpss-1983-rankin-selberg`): the functional equation of
Theorem (2.7) (printed pages 390–391), gamma multiplicativity in Theorem (3.1) (printed
pages 404–405), and their use in the proof of Proposition (9.4) (printed pages 458–462).
