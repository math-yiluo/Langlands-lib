# Independent positive-rank tempered quotient coverage: proof

Author: Worker 624.

`Langlands.Classification.temperedLanglandsQuotientCoverage` proves the
unchanged proposition
[`TemperedLanglandsQuotientCoverage`](TemperedLanglandsQuotientCoverageStatement.md).
Its entire outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`,
and its conclusion is `TemperedLanglandsQuotientCoverage.{uF, uV} F T`.
The field and carrier universe parameters remain independent.

After installing `T.topology`, the conclusion covers every positive rank and
every irreducible smooth input with carrier in `Type (max uF uV)`. It supplies
an actual `T.TemperedLanglandsDatum.{max uF uV, uF} n` and a surjective
intertwiner from its standard module onto the original input. The input needs
no additional admissibility hypothesis. There is no assertion about rank zero
or uniqueness of a kernel.

## Implemented closing proof

The Lean proof applies the published conditional theorem
[`temperedLanglandsQuotientCoverage_of`](TemperedQuotientAssembly.md).
It discharges both premises with published proofs:

- [`padicTemperedSmoothDuality`](TemperedSmoothDualityProof.md) proves
  `PadicTemperedSmoothDualityStatement.{uF, max uF uV}`. It supplies analytic
  temperedness preservation for the actual smooth contragredient, using the
  inverse central character, inversion of coefficients and Haar measures,
  and admissible smooth biduality.
- [`twistedProductOrdinaryDual`](TwistedProductOrdinaryDualProof.md) proves
  `TwistedProductOrdinaryDualClause.{uF, max uF uV} F T`. It identifies the
  smooth dual of the actual upper normalized twisted product with the
  product of the block smooth duals and negated exponents. Its proof uses
  normalized induction duality, bijectivity of the canonical smooth-dual
  tensor map, and inverse-character twist compatibility.

Both proofs are used at the saturated carrier universe `max uF uV`.
No theorem-valued argument remains in the closing theorem.

## Quotient construction supplied by the assembly

The imported assembly obtains automatic admissibility from
`CuspidalSupport.cuspidalEmbedding` and applies the maximal-cone Jacquet
quotient theorem to the input's smooth dual. It twists the whole-Levi
quotient by the negative exponent vector, factors it into irreducible
admissible block representations, and uses `glBlockTensorTempered` to
reflect its analytic temperedness to the factors. Twisting back yields a
nonzero map from the opposite Jacquet module to the tensor of the twisted
factors.

The published quotient adapter uses opposite reciprocity, block reversal,
smooth duals and inverse bidual evaluation to give a surjection from the
smooth dual of the reversed upper product onto the original input.
Ordinary product duality changes its source to the standard module of the
reversed dual blocks with exponents `-t(i.rev)`. Analytic duality makes these
blocks tempered, admissible duality makes them irreducible, and
`strictAnti_neg_reverse` supplies strict decrease of the new exponents.
Composing with the inverse product-duality equivalence gives the required
surjective intertwiner.

This construction uses the existing normalized upper block parabolic
induction with positive half-modulus covariance and right translation.
All imported definitions, target statements and proof pairs are unchanged.

## Provenance and independence

This is an internal derivation from the published Library theorems named
above; it makes no new claim of translation from external literature.
The complete project import closure was checked before reuse. It contains
none of the forbidden ordered special-segment coverage, multisegment
exhaustion, square-integrable exhaustion or regular Langlands exhaustion
proofs. The closing proof supplies the two formerly explicit duality
premises with proved results.
