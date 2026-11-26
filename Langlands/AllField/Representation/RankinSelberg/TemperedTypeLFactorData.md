# Certified L-polynomials for standard modules of tempered-type data

Module `Langlands.AllField.Representation.RankinSelberg.TemperedTypeLFactorData`,
namespace `Langlands.AllField.RankinSelberg`, over a field `F` with instances
`[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`.

## Contents

- `IsPadicRankLPolynomial ψ ν π σ P`: the relation `IsPadicSymmetricLPolynomial F ψ ν` for
  representations of arbitrary ranks, `False` at rank zero (the all-field form of the
  Library's p-adic `IsPadicRankLPolynomial`), with `isPadicRankLPolynomial_succ`,
  `.unique`, `.coeff_zero`, `.ne_zero`, `isPadicRankLPolynomial_comm` and `.congr_equiv`.
- `TemperedTypeDatum.standardModule_whittaker`, `standardModule_rankWhittaker`: the
  standard module of a datum of positive rank is of Whittaker type (published all-field
  `normalizedProductWhittakerType`).
- `TemperedTypeLPolynomialData ψ ν d e` and `temperedTypeLPolynomialData`: for data `d`,
  `e` of positive ranks, a certified polynomial of the two standard modules, certified
  polynomials of all pairs of twisted blocks, and a normalized residual `D` with
  `∏ i, ∏ j, Q i j = D * P`. This is `TwoFamilyLPolynomialData` (JPSS 1983, (3.1)(ii) in
  both families) after writing the block shapes as `succBlockShape`.
- `twoBlockShapeTailLPolynomial_dvd`: from `InducedTailLFactorAt F`, for any two-block
  shape `B` and blocks of Whittaker type, the certified polynomial of the second block
  against `σ` divides that of `Ind_B` against `σ`. The proof identifies `Ind_B` with the
  lifted pair induction of `InducedTailLFactorAt` (all-field `normalizedProductInducedEquiv`
  and `literalULiftEquiv`) and uses uniqueness of certificates, as the Library's p-adic
  lemma of the same name.
- `TemperedTypeDatum.standardTailLPolynomial_dvd`: the certified polynomial of the tail
  standard module against a test representation of Whittaker type divides that of the
  standard module (the head/tail equivalence and the previous item).
- `realPowerTwistLPolynomial`: `L(s, ν^a π × ν^b σ) = L(s + a + b, π × σ)`, from the
  published all-field `unramifiedTwistLFactor`.
- `realPowerTwistRankLPolynomial_poleFree`: from `TemperedPoleBoundStatement F`, a
  certified polynomial of `(ν^a τ, ν^b σ)` with `τ`, `σ` irreducible tempered has no zero
  in the disk of radius `q^(a + b)`. The proof untwists by `(-a, -b)`, applies the
  premise, and evaluates `Q(w) = P(q^(-a-b) w)`.

Source: JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), (3.1), (8.4), (9.3) and the
proof of (9.4), printed pages 404–405, 451–452, 455–457 and 458–462. The module follows
the Library's p-adic modules `LanglandsTypeLPolynomialData`, `LanglandsTypeTailDivisibility`
and `AnalyticTemperedTwistLPolynomialData`.
