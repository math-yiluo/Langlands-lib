# Jacquet's Lemma 3 from the classification, (8.4) and (9.3)

Module `Langlands.Representation.Conductor.OrderedUnramifiedGenerationFromPremises`.

## Main results (namespace `Langlands.Conductor`)

- `OrderedUnramifiedCorankOneGenerationAt F`: the published
  `OrderedUnramifiedCorankOneGenerationStatement` for one nonarchimedean local field `F`,
  given by its instances. Its binders after the field and its conclusion are copied
  verbatim from the published statement.
  `orderedUnramifiedCorankOneGenerationStatement_iff` (the general statement is this
  proposition at every field) and `padicOrderedUnramifiedCorankOneGenerationStatement_iff`
  (the p-adic statement is this proposition at `K.Carrier` with the canonical structures)
  hold by `Iff.rfl`.
- `orderedUnramifiedCorankOneGenerationAt_of_premises F hclass hpole htail₁ htail₂`:
  Jacquet 2012, Lemma 3, at `F`, from three results of JPSS 1983, Section 9, at `F`
  (module `AllField.Representation.RankinSelberg.TemperedTypePremisesStatement`): the
  classification of generic representations with the identification of Whittaker models
  (`GenericStandardModuleStatement`), the pole bound (8.4) (`TemperedPoleBoundStatement`)
  and the tail divisibility (9.3) (`InducedTailLFactorAt`, in two universe orders).
- `orderedUnramifiedCorankOneGeneration_of_premises`: the general statement, from these
  premises at every nonarchimedean local field.

The Library proves the three premises over p-adic fields (module
`Langlands.Representation.RankinSelberg.PadicTemperedTypePremises`). This module contains
no proof of them over other fields; for a field of positive characteristic they require
the all-field forms of the Library's p-adic classification, (8.4) and (9.3).

## Auxiliary results (namespace `Langlands.Conductor.OrderedUnramifiedTemperedType`)

- `IsPairIntegralSpan ψ abv μ π ℓ ρ ℓ' R`: `R` agrees on a right half-plane with a finite
  sum `∑_j Ψ(s, W_j, W'_j)` of corank-one integrals with `W_j` in the model of `ℓ` and
  `W'_j` in the model of `ℓ'`; closure under `zero`, `add`, `finset_sum`, `congr`, `smul`.
- `cornerPower ϖ m = diag(ϖ^m, 1, …, 1)`, `abv_det_cornerPower_inv`.
- `IsPairIntegralSpan.monomial`: if `(w, w')` converges on a half-plane, then
  `κ q^(-ms) Ψ(s, w, w')` is again an integral of a pair in the two models. Put
  `t = diag(ϖ^m, 1, …, 1)`, so `|det t| = q^(-m)`, and let `(W, W')` be the pair obtained
  by translating both arguments on the right by `t⁻¹` (the first through the embedding of
  the smaller general linear group in the larger). Substituting `g = h t` in the integral
  gives `Ψ(s, W, W') = |det t|^(s - 1/2) Ψ(s, w, w') = q^(m/2) q^(-ms) Ψ(s, w, w')`. The
  Lean proof uses this in the form `Ψ(s, w, w') = |det t⁻¹|^(s - 1/2) Ψ(s, W, W')`
  (published `corankOneIntegral_eq_sum_translate`), so
  `κ q^(-ms) Ψ(s, w, w') = κ q^(-m/2) Ψ(s, W, W')`, and the scalar `κ q^(-m/2)` is
  absorbed into the first Whittaker vector. Convergence for `(W, W')` follows from the
  right invariance of the quotient measure.
- `IsPairIntegralSpan.laurent`: the same for a Laurent polynomial in `q^(-s)`, by induction
  on Laurent polynomials.
- `sum_laurentEval_mul_eval_mul_eq_one`: if `∑_i c_i R_i = P⁻¹` in the rational functions
  and every `R_i` is regular at `z`, then `(∑_i c_i(z) R_i(z)) P(z) = 1`.
- `principalSeries_isOfInverseWhittakerType`: `I(x)` is of Whittaker type for `ψ⁻¹`
  (published all-field `normalizedProductWhittakerType` and `principalSeriesEquiv`, and
  `isOfWhittakerType_standard_iff_inverse`).

## Proof of `orderedUnramifiedCorankOneGenerationAt_of_premises`

Fix the data of the statement at `F`. As in the published
`unramifiedCorankOneLaurent_of_multiplicativity`, the measurable structures are the Borel
ones, a self-dual Haar measure `ν` for `ψ` comes from the published
`AllField.HarmonicAnalysis.padicSelfDualMeasureExists`, and `π` is of Whittaker type.

1. The published `localFieldPrincipalSeriesLFactorMultiplicativity` gives the certified
   L-polynomials `PI` of `(π, I(x))` and `Pi j` of `(π, χ_(x_j))`.
2. After identifying `q` and `abv` with the residue cardinality and normalized absolute
   value of `F` (published `eq_normalizedAbsoluteValue_ofInstances`),
   `lPolynomial_principalSeries_eq_prod` gives `PI = ∏ j, Pi j`.
3. As in the published Laurent proof, `Pi j = P(x_j X)`
   (`isCharacterLPolynomial_unramified` and uniqueness of the normalized generator), so
   `∏_j P(x_j X) = PI`.
4. `PI` is the normalized generator of the zeta values of the block `j = k = 0` of
   `(π, I(x))` at the measure `μ` (JPSS 1983, Theorem (2.7)), so `PI⁻¹` lies in their
   Laurent span: `PI⁻¹ = ∑_i c_i R_i` with Laurent polynomials `c_i` and zeta values
   `R_i`. Each `R_i` is the rational continuation of a corank-one integral `Ψ(s, w_i, w'_i)`
   of Whittaker functions of `π` and `I(x)`; by multiplicity one (published
   `whittakerSet_eq_coefficientModel` and its inverse-character form) `w_i` lies in the
   model of `ℓ` and `w'_i` in the model of `ℓ'`.
5. `IsPairIntegralSpan.laurent` writes `∑_i c_i(q^(-s)) Ψ(s, w_i, w'_i)` as a finite sum
   `∑_j Ψ(s, W_j, W'_j)` on a half-plane, and the evaluation lemma gives
   `(∑_j Ψ(s, W_j, W'_j)) PI(q^(-s)) = 1` on a half-plane where every `R_i` is regular.

Source: Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`), Lemma 3, printed
page 519; JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), Theorem (2.7), printed
pages 390–391, and Section 9, printed pages 455–462.
