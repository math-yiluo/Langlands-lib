# Reduction of the all-field functional equation to the hypothesized normalization

Module `Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction`.

The all-field port states the unequal-rank functional equation as
`Langlands.AllField.RankinSelberg.UnequalRankFunctionalEquationStatement F T n r`.
There `T : LocalFieldData F` supplies the topology, the valuative relation and the
`IsNonarchimedeanLocalField` structure. The statement fixes Borel structures `borel`,
the residue cardinality `T.residueCardinality` and the absolute value
`normalizedAbsoluteValue T`. The published target
`Langlands.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement` instead
takes ambient instances and arbitrary Borel structures (`BorelSpace`). It also takes a
hypothesized `q` with `q = Nat.card` of the residue field of `ValuativeRel.valuation F`,
and an absolute value `abv` with `abv ϖ = q⁻¹` for a uniformizing element `ϖ`
(`IsUniformizingElement`) and `abv x = 1` whenever `ValuativeRel.valuation F x = 1`.
This module proves that the first statement implies the second at
`T := LocalFieldData.ofInstances F`. It is an internal bridge with no counterpart in the
literature: JPSS 1983 work with the normalized absolute value throughout (section (0.3),
printed page 375).

## Declarations

- `discreteValuation_ofInstances`, `residueCardinality_ofInstances` (theorems, `rfl`).
  For the ambient data, `T.discreteValuation x` is the canonical isomorphism
  `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F` applied to
  `ValuativeRel.valuation F x`. `T.residueCardinality` is the cardinality of the
  residue field of the ambient valuation ring.
- `discreteValuation_eq_of_valuation_eq`: equal ambient valuations give equal discrete
  valuations.
- `discreteValuation_of_isUniformizingElement`: a uniformizing element `ϖ` has
  `T.discreteValuation ϖ = exp (-1)`. Proof: apply the uniformizing property of `ϖ`
  to the chosen uniformizer `T.uniformizer`, whose discrete valuation is `exp (-1)`.
  This gives `exp (-1) = exp (a)^m = exp (m a)` with `a = log (T.discreteValuation ϖ)`,
  so `m a = -1`. Since `v ϖ < 1` and the canonical isomorphism is strictly monotone,
  `a < 0`; hence `a = -1` by `Int.eq_one_or_neg_one_of_mul_eq_one'`.
- `ord_of_isUniformizingElement`: consequently `T.ord ϖ = 1`.
- `eq_normalizedAbsoluteValue_ofInstances`: under the three normalization hypotheses,
  `abv = normalizedAbsoluteValue (LocalFieldData.ofInstances F)`. Proof: by
  `AbsoluteValue.ext`; at `x = 0` both sides vanish. For `x ≠ 0` the uniformizing
  property gives `m` with `v x = v ϖ ^ m`. Then `T.ord x = m` (the discrete valuations
  agree and equal `exp (-m)`), so `T.normalizedAbs x = q ^ (-m)`. On the other side
  `u = x · (ϖ^m)⁻¹` has valuation one, so `abv x = abv u · abv ϖ ^ m = (q⁻¹)^m = q^(-m)`.
- `localFieldUnequalRankFunctionalEquation_of_allField` (theorem): if
  `UnequalRankFunctionalEquationStatement F (LocalFieldData.ofInstances F) n r` holds
  for every field with nonarchimedean local-field instances and all ranks, then
  `LocalFieldUnequalRankFunctionalEquationStatement.{uF, uV, uW}` holds. Proof: introduce
  the target's binders. Replace each of the four measurable-space instances by `borel`
  using `BorelSpace.measurable_eq`; `BorelSpace` is a proposition, so the instance proofs
  agree. Substitute `q = T.residueCardinality` and
  `abv = normalizedAbsoluteValue T` by the lemmas above, and apply the hypothesis. The
  instance `Measure.IsMulRightInvariant (unipotentHaar F n)` is passed explicitly,
  because the ported statement's topology `(ofInstances F).topology` agrees with the
  ambient one only after unfolding `ofInstances`. The extra target instances
  `T2Space F` and `TotallyDisconnectedSpace F` are not used.
