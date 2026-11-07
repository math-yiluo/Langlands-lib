# Classification and integral epsilon factors of generic pairs

Author: Worker 1411. This module, in namespace `Langlands.RankinSelberg`,
defines the proposition `GenericLanglandsPairEpsilonFactorComparisonStatement`.
For a pair of generic representations of p-adic general linear groups, it
compares two existing epsilon relations on the same actual pair:

- the classification relation `IsLanglandsPairEpsilonFactor` (module
  `LanglandsFactors`), defined through square-integrable Langlands data;
- the integral relation `IsPadicSymmetricEpsilonFactor` (module
  `PadicPairFactors`), defined through the local functional equation of the
  pair itself.

The statement says that every value certified by the first relation satisfies
the second. The module also proves three corollaries that hold under the
statement. The statement itself is not proved.

## The statement

`GenericLanglandsPairEpsilonFactorComparisonStatement.{uF, uV, uW}` quantifies
over:

- every prime `p` and every `F : PadicField.{uF} p`, with its canonical
  topological data;
- every `ψ : UnitaryAdditiveCharacter F.Carrier`;
- every `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`;
- all `r t : ℕ`;
- every `π : SmoothRep.{0, uF, max uF uV} ℂ (GL_(r+1)(F))` and every
  `σ : SmoothRep.{0, uF, max uF uW} ℂ (GL_(t+1)(F))`.

Its hypotheses are `Whittaker.IsGeneric ψ r π.representation` and
`Whittaker.IsGeneric ψ t σ.representation`. Its conclusion is: for every
`e : ℂˣ × ℤ`,

`IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν.val π σ e →
IsPadicSymmetricEpsilonFactor F ψ ν.val π.representation σ.representation e`.

The ranks `r + 1` and `t + 1` are arbitrary positive integers, in either
order. There is no existence premise and no comparison premise. In particular
there is no premise that the two relations agree, and no premise comparing
Whittaker models. The only premise about `e` is the existing classification
certificate. The statement does not assert that such a certificate exists.

## Meaning of the two relations

Both relations are the published ones; this module does not change either.

**Classification relation.**
`IsLanglandsPairEpsilonFactor F ψ ν π σ e` is the conjunction of:

1. some `SquareIntegrableLanglandsDatum` `d` of rank `r + 1` has
   `d.IsLanglandsQuotient π`;
2. some such datum `d'` of rank `t + 1` has `d'.IsLanglandsQuotient σ`;
3. for *every* pair of such data, `IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e`.
   This says there is a family `b i j` of block epsilon factors with
   `IsPadicRankEpsilonFactor F ψ ν τ_i μ_j (b i j)` for all blocks `τ_i` of
   `d` and `μ_j` of `d'`, and `e = epsilonFactorProduct b`.

So `e` is the product of the JPSS epsilon factors of all block pairs of the
Langlands data. The relation is about the blocks, not about Whittaker
functionals of `π` and `σ`.

**Integral relation.**
`IsPadicSymmetricEpsilonFactor F ψ ν π σ e` is
`IsPadicPairEpsilonFactor F ψ ν π σ e` if `t ≤ r`, and
`IsPadicPairEpsilonFactor F ψ ν σ π e` otherwise: the larger rank comes
first, and equal ranks keep the given order. `IsPadicPairEpsilonFactor` uses
the canonical residue cardinality `q` and normalized absolute value of `F`,
and unfolds to `IsPairEpsilonFactor` (module `EpsilonFactor`). That relation
asks for:

- nonzero Whittaker functionals of both representations, with the standard
  character of `ψ` for the larger rank and the inverse standard character
  (`ψ⁻¹`) for the other;
- for every compatible quotient measure and all such nonzero functionals, the
  JPSS local functional equation (JPSS 1983, Theorem 2.7(iii), printed page
  391) with the monomial `c q^(-ms)`.

Each relation determines `e` (`IsLanglandsPairEpsilonFactor.unique`,
`IsPadicSymmetricEpsilonFactor.unique`). Neither relation is defined through
the other, so the statement is a genuine comparison.

## Normalization

- **Monomial.** `e = (c, m)` represents `ε(s, π × σ, ψ) = c q^(-ms)` in both
  relations, with the same `q`. The classification value is
  `epsilonFactorProduct b`: coefficients multiplied, exponents added.
- **Character.** The same `ψ` occurs in both relations and in every block
  factor. `ψ` is nontrivial by its type: `UnitaryAdditiveCharacter` bundles
  continuity, unit-circle values and `toAddChar ≠ 1`. No conductor condition
  is imposed.
- **Inverse-character convention.** The hypotheses ask for a nonzero
  functional for the standard character of `ψ`, for both representations.
  The integral relation uses the inverse standard character for the
  representation of smaller rank. These hypotheses suffice, so the convention
  imposes no extra condition:
  - The two functional spaces of one representation are linearly
    equivalent (`characterChangeFunctionalEquiv` at `-1`, as in
    `isOfWhittakerType_standard_iff_inverse` of `WhittakerGammaAdapters`).
  - The published `genericSymmetricEpsilonData_isPadic` constructs integral
    epsilon data, in either rank order, from exactly the hypotheses
    `IsGeneric ψ` for both representations.
- **Measure.** `ν` ranges over the published subtype `SelfDualHaar` of Haar
  measures self-dual for `ψ`, and `ν.val` is passed to both relations. This is
  the normalization of `LanglandsPairEpsilonFactorExistenceStatement`,
  `GenericLanglandsQuotientLFactorStatement` and `GammaMultiplicativityStatement`.
  It is also the hypothesis of `genericSymmetricEpsilonData`. Both relations
  accept any additive Haar measure, so self-duality restricts the claim, not
  the relations. The claim for other Haar measures is not made. The statement
  does not assert that a self-dual measure exists.

## Source audit

G. Henniart, *Une caractérisation de la correspondance de Langlands locale
pour GL(n)*, Bull. Soc. Math. France 130 (2002), 587-602. Registered source
`henniart-2002-characterization`, SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
Read from the text layer.

- **§1.2, printed pages 588-589 (PDF pages 2-3).** For irreducible smooth
  `π` of `GL_n(F)` and `π'` of `GL_n'(F)`, `L(s, π × π')` and
  `ε(s, π × π', ψ)` denote "les facteurs définis par Jacquet,
  Piatetski-Shapiro et Shalika [6] ou par Shahidi". The `ε` factors have the
  form `α q^(-ms)` with `α ∈ ℂ×` and `m ∈ ℤ`. Also
  `γ = ε L(1 − s, ∨)/L(s)`.
- **§2.8, printed page 596 (PDF page 10).** Henniart writes an irreducible
  class as `J(π_1, …, π_r)`, the unique irreducible quotient of
  `i(π_1, …, π_r)` with essentially square-integrable `π_i` and
  `α(π_1) ≥ ⋯ ≥ α(π_r)`. For `π = ∑_(i∈I) π_i` and `π' = ∑_(j∈J) π'_j`, the
  final display gives
  `ε(s, π × π') = ∏_(i,j) ε(s, π_i × π'_j, ψ)`, together with the same
  products for `L` and `γ`.

For a generic pair, the left side of this display is, by §1.2, the JPSS
factor of the pair itself. The display then asserts the implication of this
statement:

- its right side is the classification value `e`;
- its left side is the value certified by `IsPadicSymmetricEpsilonFactor`.

Henniart states this without proof and refers to [1] and [6, Intr.]; [6] is
JPSS 1983.

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983). Registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page = PDF page + 365. Read from the page images.

- **(3.1), printed pages 404-405 (PDF pages 39-40).** `π` and `σ_i` are of
  Whittaker type, and `σ = Ind(G_t, Q; σ_1, …, σ_p)` with `Q` the lower
  standard parabolic subgroup. Display (2) sets
  `γ(s, π × σ, ψ) = ε(s, π × σ, ψ) L(1 − s, π^ι × σ^ι)/L(s, π × σ)`.
  The Theorem gives (i) `γ(s, π × σ, ψ) = ∏ γ(s, π × σ_i, ψ)` and (ii)
  `L(s, π × σ) ∈ ∏ L(s, π × σ_i) ℂ[q^(-s), q^s]`.
- **Remark (3.3), printed pages 405-406.** If `π^0` is the quotient of `π`
  realized in its Whittaker model, then `L(s, π × σ) = L(s, π^0 × σ)` and
  `γ(s, π × σ, ψ) = γ(s, π^0 × σ, ψ)`.
- **(9.4), printed pages 458-459 (PDF pages 93-94).** Display (3) of the
  Proposition: `L(s, ξ × η) = ∏ L(s, π_i × σ_j)` for the standard modules
  `ξ`, `η` of tempered data. A generic `π` has the same Whittaker model as its
  `ξ`, which gives display (4), `L(s, ξ × η) = L(s, π × σ)`. This passage
  concerns only the L-factor; the proof on page 459 uses Theorem (3.1).
- **Introduction (0.1), displays (15)-(16), printed pages 371-372.** An
  epsilon identity appears only as an axiom suggested for a conjectural
  correspondence.

No passage of JPSS states the epsilon comparison. They give its ingredients:

- multiplicativity of `γ` under induction (3.1);
- independence from the choice of Whittaker quotient (3.3);
- the identification of the Whittaker models of a generic representation and
  its standard module (9.4);
- the formula `ε = γ L(s)/L(1 − s, dual)`.

A proof is expected to combine these with the corresponding product formulas
for L-factors. This route is only a lead for the proof task and is not checked
here. In particular, the display (9.4)(4) is not cited as an epsilon result.

Errata check. The project notes of the pinned Library record no erratum to
JPSS 1983 and none affecting the Henniart passages cited above (§1.2 and
§2.8). They do record two misprints elsewhere in Henniart 2002:

- §2.6, printed page 595, prints the dual of `St_n(ρ)` with `ρ` in place of
  `ρ^∨`; the corrected form is `St_n(ρ)^∨ ≅ St_n(ν^(1-n) ρ^∨)`
  (Zelevinsky 1980, 9.4). See `notes/henniart/audit.md`, lines 261-269, and
  `notes/henniart/llc-specification-coverage.md`, lines 244-250.
- §4.5 restates Theorem 1.8(ii) with `τ ∈ G(r)` and prints "⊗" for "×"
  (`notes/henniart/llc-specification-coverage.md`, lines 244-250).

Neither correction enters this statement. It compares two representation-side
epsilon relations built from existing block epsilon predicates, and it uses no
explicit formula for the dual of a square-integrable block. The §2.6 formula
is used in the factor calculation that follows it in Henniart's text.

## Universes

- **Carriers.** `π` and `σ` have the carrier universes `max uF uV` and
  `max uF uW` that `IsLanglandsPairEpsilonFactor` itself requires. These are
  also the binders of `LanglandsPairEpsilonFactorExistenceStatement` and
  `GenericLanglandsQuotientLFactorStatement`. The field universe `uF` and the
  parameters `uV`, `uW` are independent.
- **Certificate.** The premise is the certificate at `.{uF, uV, uW}`, with
  blocks in `uV` and `uW`. This is the most general instance:
  - At `.{uF, max uF uV, max uF uW}` the premise is the saturated certificate
    produced by `LanglandsPairEpsilonFactorExistenceStatement` and by
    `langlandsPairEpsilonFactorOfClassification`; the binders are unchanged
    because `max uF (max uF uV)` is the level `max uF uV`. The third
    corollary below uses this instance.
  - At `uV = uW = uA`, the instance is the one used by
    `Correspondence.IsAutomorphicPairEpsilonFactor`, which asks for
    `IsLanglandsPairEpsilonFactor.{uF, uA, uA}` on carriers in `max uF uA`.
- **Not claimed.** The conclusion does not mention block universes, and no
  universe-lowering of Langlands data is asserted.

## Hypotheses

- **Generic scope.** `Whittaker.IsGeneric ψ n π` (module
  `Whittaker/GeneralLinear`) is the conjunction:
  - `Representation.IsIrreducible π`;
  - `IsAdmissible π`;
  - `HasFunctional` for the standard character of `ψ`: a nonzero standard
    Whittaker functional.

  So the hypotheses consist of irreducibility, admissibility and genericity
  for `ψ` of each representation. This is the hypothesis form of
  `GenericLanglandsQuotientLFactorStatement` and of `genericSymmetricEpsilonData`.
- **No presentation hypothesis.** No Langlands datum is supplied
  separately. The certificate already contains presenting data, and its
  third conjunct covers every presenting datum pair.
- **No smaller class.** The pairs are not restricted to supercuspidal or
  square-integrable representations. The Library proves the comparison for
  supercuspidal pairs, for every Haar measure and without genericity
  hypotheses: `IsLanglandsPairEpsilonFactor.isPadicSymmetricEpsilonFactor_of_isSupercuspidal`
  in `SupercuspidalLanglandsEpsilon`. This module does not use it.
- **Field.** `F` is a p-adic field (`PadicField`), because both relations
  and the canonical topological data `F.canonicalTopologicalData` are stated
  for `PadicField`.

## No new objects

The statement uses only existing objects: the two relations, the published
`SelfDualHaar` subtype, `Whittaker.IsGeneric`, and in the corollaries the
published constructed data `genericSymmetricEpsilonData`. It defines no
transport or comparison object, so there are no construction obligations.

## Corollaries

Each corollary takes the statement `h` as a hypothesis. It proves nothing
about the statement itself.

- `eq_genericSymmetricEpsilonData`: for generic `π`, `σ` and a classification
  certificate of `e`,
  `e = genericSymmetricEpsilonData F ψ ν.val ν.property π.representation σ.representation hπ hσ`.
  Proof: `IsPadicSymmetricEpsilonFactor.unique` applied to the conclusion of
  `h` and `genericSymmetricEpsilonData_isPadic`.
- `isLanglandsPairEpsilonFactor_iff`: if a generic pair has some
  classification epsilon factor `e₀`, then for every `e` the classification
  and integral relations are equivalent. The reverse direction uses
  uniqueness of the integral factor to identify `e` with `e₀`.
- `isLanglandsPairEpsilonFactor_genericSymmetricEpsilonData`: from
  `LanglandsPairEpsilonFactorExistenceStatement.{uF, uV, uW}` and the
  statement at `.{uF, max uF uV, max uF uW}`, the published data
  `genericSymmetricEpsilonData` of a generic pair satisfies
  `IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW}`. The
  irreducibility and admissibility inputs of the existence statement are the
  first two conjuncts of `IsGeneric`.

## Combination with the existence and L-factor targets

The classification gamma relation `IsLanglandsPairGammaFactor` (module
`LanglandsGammaFactor`) says that `G` equals
`rationalGammaExpression (residueReflection F) e.1 e.2 P Pdual` for some `e`,
`P` and `Pdual` with:

- `IsLanglandsPairEpsilonFactor F ψ ν π σ e`;
- `IsLanglandsPairLPolynomial F ψ ν π σ P`;
- `IsLanglandsDualPairLPolynomial F ψ ν π σ Pdual`, the classification
  L relation of the smooth contragredients with `ψ.scale (-1)`.

The integral gamma factor of a generic pair has the same shape. By
`genericSymmetricGammaFactor_eq_expression` (module
`PadicGenericGammaExpression`), it is the expression of
`genericSymmetricEpsilonData`, `genericSymmetricLPolynomial` and
`genericSymmetricDualLPolynomial`. The integral relation
`IsPadicSymmetricGammaFactor` is used by `GammaMultiplicativityStatement`
(proved as `gammaMultiplicativity`) and by
`HighlyRamifiedGammaStabilityStatement`. Also,
`symmetricGammaExpression` (module `SymmetricGammaExpressionProof`)
characterizes it as this expression, for any certified epsilon factor and
original and dual L-polynomials.

For a generic pair and a self-dual `ν`, the three components can be matched
as follows. Only step 1 is the content of this statement.

1. **Epsilon.** This statement and `eq_genericSymmetricEpsilonData` give
   `e = genericSymmetricEpsilonData …`. Existence of `e` is the separate
   target `LanglandsPairEpsilonFactorExistenceStatement`, at the saturated
   instance (third corollary).
2. **L-polynomial.** `IsLanglandsPairLPolynomial` is the L relation of the
   standard modules of tempered data. `GenericLanglandsQuotientLFactorStatement`
   (JPSS (9.4)(4)) gives an L-polynomial of the standard modules that is also
   an `IsPadicSymmetricLPolynomial` of `π` and `σ` themselves. Uniqueness of
   the integral L-polynomial then identifies `P` with
   `genericSymmetricLPolynomial`. Existence of `P` is
   `LanglandsPairLFactorExistenceStatement`.
3. **Dual L-polynomial.** The same two L targets would be applied to the
   contragredient pair with `ψ.scale (-1)`. That needs:
   - the contragredients to be generic for `ψ.scale (-1)`. In
     `SmoothDualPairFactors`, `isOfWhittakerType_smoothContragredient` gives
     Whittaker type of the smooth dual for the inverse standard character of
     `ψ`. Irreducibility of the smooth dual is not checked here;
   - a self-dual measure for `ψ.scale (-1)`.

   Then `isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient`
   relates the result to `genericSymmetricDualLPolynomial_isPadic`. That
   theorem is stated for the inverse-transpose pullbacks with `ψ.scale (-1)`.
   The relating step uses the equivalence `inverseTransposeSmoothDualEquiv`,
   built on the proved `gelfandKazhdanContragredient`. These steps are not
   checked here.
4. **Gamma.** With the three identifications, the classification `G`
   equals the integral generic gamma factor, so stability and
   multiplicativity apply to it.

Steps 2-4 are not claimed or proved here; they are recorded for the consumer
`Correspondence.FullGammaCompatibility.IsAutomorphicPairGammaFactor`, whose
epsilon component is `IsLanglandsPairEpsilonFactor`.

## Lean checks

`lean_check` of the module with declaration
`Langlands.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonStatement`:

- 0 errors and 0 warnings.
- The declaration is a definition returning `Prop`, with universe parameters
  `uF`, `uV`, `uW`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.

The same checks with declarations
`GenericLanglandsPairEpsilonFactorComparisonStatement.isLanglandsPairEpsilonFactor_iff`
and
`GenericLanglandsPairEpsilonFactorComparisonStatement.isLanglandsPairEpsilonFactor_genericSymmetricEpsilonData`
report theorems with the same three axioms.
