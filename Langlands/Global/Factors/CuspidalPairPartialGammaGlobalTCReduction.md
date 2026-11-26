# The totally complex partial equation of cuspidal pairs from the global Rankin–Selberg theory

Module `Langlands.Global.Factors.CuspidalPairPartialGammaGlobalTCReduction`.

## 1. Content and provenance

This module is the totally complex form of the published reduction
`Langlands.Global.cuspidalPairPartialGammaGlobalReduction`
([`CuspidalPairPartialGammaGlobalReduction`](CuspidalPairPartialGammaGlobalReduction.md)).
That reduction derives the partial functional equation (G'),
`Langlands.Global.CuspidalPairPartialGammaEquationStatement`, from ten statements of the global
Rankin–Selberg theory. Here the conclusion is the totally complex form of (G'),
`Langlands.Global.CuspidalPairPartialGammaEquationTCStatement`
([`CuspidalPairPartialGammaEquationTCStatement`](CuspidalPairPartialGammaEquationTCStatement.md)).
Eight premises are the same unrestricted statements. The two semi-local equations are replaced
by their totally complex forms `UnequalSemilocalEquationTCStatement` and
`EqualSemilocalEquationTCStatement`
([`SemilocalEquationTCStatements`](../RankinSelberg/SemilocalEquationTCStatements.md)).

The module contains:

* the statement `Langlands.Global.CuspidalPairPartialGammaGlobalTCReductionStatement.{u, uQ}`
  (Section 2) and the theorem `Langlands.Global.cuspidalPairPartialGammaGlobalTCReduction`, which
  proves it;
* in the namespace `Langlands.Global.CuspidalPairPartialGammaTC`:
  * three lemmas stating that each unrestricted statement implies its totally complex form
    (Section 3);
  * two auxiliary Prop-valued definitions, `UnequalPackageTCStatement` and
    `EqualPackageTCStatement`, and the theorems `unequalPackageTC` and `equalPackageTC`, which
    prove them from the premises (Section 4). `EqualPackageTCStatement` quantifies
    `EqualPackageAt F` over the totally complex number fields `F`.

The theorem is a reduction: it does not prove the totally complex form of (G'). Section 6
says which of its premises the Library proves. It belongs to the restriction of the global
statements on the route to the local correspondence to totally complex base fields
(`CuspidalPairFunctionalEquationTCStatement.md` §4). It gives no unconditional proof of the
unrestricted (G').

**Why only the semi-local premises change.** Of the ten premises of the published reduction,
only `UnequalSemilocalEquationStatement` and `EqualSemilocalEquationStatement` involve real
places: their conclusions contain the archimedean expressions `infiniteL`, `dualInfiniteL`
and `infiniteEpsilon`, products over the real and the complex places. The other eight
premises are global statements about the integrals and their Euler products. They contain no
archimedean local factor. Over a totally complex field the real-place products are empty, so
the two semi-local equations need the archimedean local theory only for `GL_n(ℂ)`.

**Source.** J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004)
(`cogdell-2004-analytic-theory-gln`; PDF page = printed page + 3), proof of Theorem 4.1,
printed pp.219–220. The argument is that of the published reduction, whose Markdown explains
the correspondence with the source. Cogdell treats every number field. Totally complex fields
are a special case.

**Provenance (internal).** The split of the argument into premises is that of the published
reduction. Restricting the two semi-local premises and the conclusion to totally complex
fields is ours.

## 2. The statement

`CuspidalPairPartialGammaGlobalTCReductionStatement.{u, uQ}` is the implication

```text
UnequalAnalyticStatement.{u} → UnequalUnfoldingStatement.{u} →
UnequalEulerFactorizationStatement.{u, uQ} → UnequalDualEulerFactorizationStatement.{u, uQ} →
UnequalSemilocalEquationTCStatement.{u, uQ} →
EqualAnalyticStatement.{u} → EqualUnfoldingStatement.{u} →
EqualEulerFactorizationStatement.{u, uQ} → EqualDualEulerFactorizationStatement.{u, uQ} →
EqualSemilocalEquationTCStatement.{u, uQ} →
CuspidalPairPartialGammaEquationTCStatement.{u, uQ}
```

All premises are in the namespace `Langlands.Global.RankinSelbergGlobal`. They are in the
order of `CuspidalPairPartialGammaGlobalReductionStatement`: premises 5 and 10 are the
totally complex forms, and the other eight are the unrestricted statements, explained in §2
of [`CuspidalPairPartialGammaGlobalReduction`](CuspidalPairPartialGammaGlobalReduction.md).

## 3. The unrestricted statements imply their totally complex forms

Each totally complex form is its original with one more instance argument
`[NumberField.IsTotallyComplex F]` after `[NumberField F]`, the rest verbatim. So the original
implies it at the same universe levels: apply the original to the same field and forget the
instance, `fun h F _ _ _ _ => h F`. The module records this for the three statements involved:

* `unequalSemilocalEquationTC_of_unrestricted`: `UnequalSemilocalEquationStatement` implies
  `UnequalSemilocalEquationTCStatement`;
* `equalSemilocalEquationTC_of_unrestricted`: `EqualSemilocalEquationStatement` implies
  `EqualSemilocalEquationTCStatement`;
* `cuspidalPairPartialGammaEquationTC_of_unrestricted`: `CuspidalPairPartialGammaEquationStatement`
  implies `CuspidalPairPartialGammaEquationTCStatement`.

In particular a proof of either unrestricted semi-local equation discharges the corresponding
premise of the reduction.

## 4. The packages

* `UnequalPackageTCStatement` is the published auxiliary definition
  `CuspidalPairPartialGammaGlobal.UnequalPackageStatement` with the instance argument
  `[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, the rest verbatim. It
  takes the binders and hypotheses of (G') with `t < r` and asserts meromorphic `I`, `J`,
  `A`, `B` with `I(s) = J(1 - s)` and `A`, `B` nonzero off a discrete set, the partial Euler
  factorizations `I = A ∏_(v ∉ S) L_v` and `J = B ∏_(v ∉ S) L∨_v` on a right half-plane, and
  the semi-local equation
  `L_∞(s) B(1 - s) = (∏_(v ∈ S) G_v(q_v^(-s))) ε_∞(s) L∨_∞(1 - s) A(s)` off a discrete set.
  Its meaning is explained in §3 of the published reduction's Markdown.
* `unequalPackageTC` proves it from the four unrestricted unequal-rank premises and
  `UnequalSemilocalEquationTCStatement`. The tactic proof is that of the published
  `unequalPackage`, with one more introduced instance. All premises are applied to the same
  field `F`. The unrestricted premises apply because `F` is a number field. The semi-local
  premise applies because the instance `NumberField.IsTotallyComplex F` is in scope.
* `EqualPackageTCStatement` and `equalPackageTC` are the same for `t = r`, from
  `EqualPackageStatement` and `equalPackage`.

## 5. The proof of the reduction

`cuspidalPairPartialGammaGlobalTCReduction` is the proof of the published
`cuspidalPairPartialGammaGlobalReduction`, with the totally complex packages in place of the
unrestricted ones and one more introduced instance. It builds both packages from the ten
premises, introduces the binders of the totally complex (G'), and splits by
`lt_trichotomy t r`. It uses the published lemmas of the namespace
`Langlands.Global.CuspidalPairPartialGammaGlobal` unchanged: `meromorphicOn_prod_inv_denominator`,
`exists_partialEquation`, `partialEulerFactor_comm` and the symmetry lemmas
`realPairLFactor_denominator_comm`, `complexPairLFactor_denominator_comm`,
`realPairEpsilon_comm` and `complexPairEpsilon_comm`. The packages use
`isStandardAdditiveCharacter_complex`, `equalPoleSet_finite` and
`meromorphicOn_of_hasAtMostSimplePolesIn`.

* `t < r`: the unequal package and `exists_partialEquation`.
* `t = r`: the equal package after `subst`, and `exists_partialEquation`.
* `t > r`: the unequal package applied with the two realizations and their parameter lists
  exchanged, then `partialEulerFactor_comm`, the definition of
  `IsPadicSymmetricGammaFactor` and the symmetry lemmas, as in §4 of the published
  reduction's Markdown. The field `F` is unchanged, so the package still applies over a
  totally complex field.

The real-place clauses are kept verbatim. Over a totally complex field they are vacuous, and
the proof never uses that fact: it handles the real places exactly as the published proof
does.

## 6. The retained premises

The proof uses no hypothesis other than the ten premises. The Library proves the eight
unrestricted ones: `UnequalAnalyticStatement`, by
`Langlands.Global.RankinSelbergGlobal.UnequalAnalytic.unequalAnalyticStatement_proof`, and
`EqualAnalyticStatement`, by
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic.equalAnalyticStatement_proof`;
`UnequalUnfoldingStatement` and `EqualUnfoldingStatement`, by
`unequalUnfoldingStatement_proof` and `equalUnfoldingStatement_proof` (modules
`Langlands.Global.RankinSelberg.UnequalUnfoldingProof` and `…EqualUnfoldingProof`);
`UnequalEulerFactorizationStatement` and `EqualEulerFactorizationStatement`, by
`unequalEulerFactorization` and `equalEulerFactorization` (modules
`…UnequalEulerFactorizationProof` and `…EqualEulerFactorizationProof`); and
`UnequalDualEulerFactorizationStatement` and `EqualDualEulerFactorizationStatement`, by
`unequalDualEulerFactorization` and `equalDualEulerFactorization` (modules
`…UnequalDualEulerFactorizationProof` and `…EqualDualEulerFactorizationProof`). A proof of
the totally complex (G') by this route needs proofs of the two totally complex semi-local
equations, or of their unrestricted forms (Section 3). The Library derives the two totally
complex semi-local equations from further premises in
`Langlands.Global.RankinSelberg.UnequalSemilocalEquationTCReduction` and
`Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReductionTC`.
