# The unequal-rank JPSS functional equation over every nonarchimedean local field

Author: Worker 5550. This module defines one proposition,
`Langlands.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement`
(universes `uF`, `uV`, `uW`). It is a statement only: nothing here proves it.
The separately planned reduction `Conductor.TrivialCharacterEpsilonReduction`
is intended to use it as an explicit premise. That reduction is not included in
this contribution.

## Statement

The proposition quantifies, in this order:

- a field `F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`,
  `IsNonarchimedeanLocalField F`, `T2Space F`, `TotallyDisconnectedSpace F` and a
  measurable structure with `BorelSpace F`. Any characteristic is allowed, and
  there is no `PadicField` restriction;
- ranks `n r : ℕ`. The representations live on `GL_(n+1)(F)` and `GL_(r+1)(F)`;
- measurable structures with `BorelSpace` on `GL_(n+1)(F)`, on its upper unipotent
  subgroup `upperUnipotent (n + 1) F` and on `LeftUnipotentQuotient n F`;
- `q : ℕ` equal to the cardinality of the residue field of the valuation ring;
- `abv : AbsoluteValue F ℝ` and a unit `ϖ` with
  `IsUniformizingElement (ValuativeRel.valuation F) ϖ`, `abv ϖ = q⁻¹` and
  `abv x = 1` whenever `ValuativeRel.valuation F x = 1`;
- `hnr : n < r`;
- `ψ : UnitaryAdditiveCharacter F`;
- an instance `Measure.IsMulRightInvariant (unipotentHaar F n)`, a measure `μ` on
  `LeftUnipotentQuotient n F` with
  `IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ`;
- an additive Haar measure `ν` on `F` with `IsSelfDual ψ ν`;
- carriers `V : Type uV` and `W : Type uW`, complex vector spaces, with
  `π : Representation ℂ (GeneralLinear (r + 1) F) V` and
  `σ : Representation ℂ (GeneralLinear (n + 1) F) W`;
- `IsOfWhittakerType r (standardCharacter ψ r) π` and
  `IsOfWhittakerType n (inverseStandardCharacter ψ n) σ`;
- functionals `ℓ : glFunctionals ψ r π` and `ℓ' : glInverseFunctionals ψ n σ`
  with `ℓ.val ≠ 0` and `ℓ'.val ≠ 0`.

The conclusion is the published

```
UnequalRankFunctionalEquationConclusion hnr q ψ abv μ ν π σ ℓ ℓ'
```

of module [`FunctionalEquationStatement`](FunctionalEquationStatement.md). Spelled
out, there are `ζ c : ℂˣ`, `m : ℤ` and polynomials `P`, `Pdual` such that
`HasModelMinusOneScalar σ ℓ' ζ` holds and, for every block decomposition
`r = n + (j + k + 1)`:

- `P` is the normalized generator of the block-`j` zeta values of the pair;
- `Pdual` is the normalized generator of the block-`k` dual zeta values, which use
  `ψ⁻¹` and the right translate of `W̃` by `diag(1_(n+1), w_(r-n))`;
- for every pair of coefficient-model vectors, both zeta integrals have rational
  continuations `R` and `Rdual`, and they satisfy the published
  `NormalizedFunctionalEquation q P Pdual ζ c r m R Rdual`.

So one epsilon monomial `c X^m` (the factor `c q^(-ms)`) and one pair of
L-factor generators serve every block `j`.

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), 367–464; registered source
`jpss-1983-rankin-selberg`, file
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The scan has no text layer. Printed page `p` is PDF page `p − 365`. The following
pages were rendered and read.

- (0.3), printed page 375 (PDF 10): "The ground field `F` is local,
  non-archimedean." No restriction on the characteristic is made, so the source
  theorem covers every nonarchimedean local field. This is why `F` here is
  arbitrary rather than a `PadicField`.
- Theorem (2.7)(iii), printed page 391 (PDF 26), display (2): "if `t ≤ r − 1`, set
  `k = r − t − 1 − j`. Then
  `Ψ(1 − s, ρ(w_{r,t}) W̃, W̃'; k)/L(1 − s, π^ι × (π')^ι)
  = ω_{π'}(−1)^{r−1} ε(s, π × π', ψ) Ψ(s, W, W'; j)/L(s, π × π')`, the factor
  `ε(s, π × π', ψ)` being independent of `j`." The factor has the form
  `c q^(−ns)` (part (iii), first sentence), and the `L`-factors are those of
  part (ii) on pages 390–391, with `L(s, π × π')` "independent of `j`".

The source's `π` on `G_r` and `π'` on `G_t`, `t < r`, are the Lean `π` on
`GL_(r+1)` and `σ` on `GL_(n+1)`, so the source's `(r, t)` is `(r + 1, n + 1)`
and its `k = r − t − 1 − j` is the Lean `k` with `r = n + (j + k + 1)`. The
translation of every other ingredient (Whittaker type for `ψ` and `ψ̄`, the
integrals `Ψ(s, W, W'; j)`, `W̃`, `ρ(w_{r,t})`, the self-dual measure on the
rectangular blocks, the sign `ω_{π'}(−1)^{r−1}` through `HasModelMinusOneScalar`,
and the normalized generators) is the one recorded for the p-adic
`UnequalRankFunctionalEquationStatement` in
[`FunctionalEquationStatement.md`](FunctionalEquationStatement.md), sections
"The source statement", "Dual data", "Unequal rank" and "Measures": this module
uses the same conclusion `UnequalRankFunctionalEquationConclusion`, unchanged.

## Relation to the p-adic statement

This proposition is derived from the published
`UnequalRankFunctionalEquationStatement F T n r` of the same module family. The
conclusion and the quantifiers from `hnr` on are the same, in the same order.
Only the field and its normalizations differ.

- **The field.** The p-adic statement fixes `F : PadicField p` with
  `T : F.TopologicalData` and installs the topology, valuation, local-field
  structure and Borel structures with `letI`. Here every nonarchimedean local field
  occurs, with its structures as instance arguments, as in the published
  `Conductor.ConductorExponentStatement` and
  `Conductor.TrivialCharacterEpsilonStatement`. The `BorelSpace` hypotheses force
  each measurable structure to be the Borel one, as the p-adic `letI` do.
  `T2Space F` and `TotallyDisconnectedSpace F` hold for every nonarchimedean local
  field, so these two binders do not narrow the scope; they keep the binder list
  of the host statements.
- **`q` and `abv`.** The p-adic statement uses `T.residueCardinality` and
  `normalizedAbsoluteValue T`. Here `q` is any natural number equal to the residue
  cardinality, and `abv` is any absolute value with `abv ϖ = q⁻¹` for a uniformizer
  `ϖ` and `abv = 1` on valuation units. Every `x ≠ 0` is `ϖ^k u` with `u` a unit,
  so these conditions determine `abv x = q^(−k)`: `abv` is the normalized absolute
  value. Every nonarchimedean local field has a uniformizer (published
  `GeneralLinear.Iwasawa.exists_isUniformizingElement`, module `Whittaker.Iwasawa`), so these
  hypotheses can be met. The uniformizer occurs only to pin down `abv`.

The proposition has the conclusion of the p-adic statement and covers every
nonarchimedean local field. It does not repeat the equal-rank case, the analytic
parts (i)–(ii) of Theorem (2.7) as separate statements, or the existence of
compatible quotient measures and self-dual measures; the first two are not needed
by the reduction that uses this statement.

## Imports

`Langlands.Representation.RankinSelberg.FunctionalEquationStatement` (for
`UnequalRankFunctionalEquationConclusion`, `IsOfWhittakerType`, the functional
spaces and the measures) and `Langlands.Representation.Whittaker.Iwasawa` (for
`IsUniformizingElement`; the namespace `Langlands.GeneralLinear.Iwasawa` is opened).

## Lean checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiles the
module with no errors or warnings. Inspection of the declaration reports a
definition returning `Prop`, universe parameters `uF uV uW`, and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
