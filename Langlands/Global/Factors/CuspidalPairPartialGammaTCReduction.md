# The totally complex completed equation of cuspidal pairs from the totally complex partial equation

Module `Langlands.Global.Factors.CuspidalPairPartialGammaTCReduction`.

## 1. Content and provenance

All declarations below are in namespace `Langlands.Global`. The module defines no new
proposition other than the reduction statement. It contains:

* the statement `CuspidalPairPartialGammaTCReductionStatement.{u, uQ}`:
  ```
  CuspidalPairPartialGammaEquationTCStatement.{u, uQ} →
    CuspidalPairCompletedEquationTCStatement.{u, uQ}
  ```
  Both sides are imported unchanged. The premise is the totally complex (TC) form of the
  published (G') = `CuspidalPairPartialGammaEquationStatement.{u, uQ}`, defined in module
  [`CuspidalPairPartialGammaEquationTCStatement`](CuspidalPairPartialGammaEquationTCStatement.md).
  The conclusion is the TC form of the completed equation
  `CuspidalPairCompletedEquationStatement`, defined in module
  [`CuspidalPairFunctionalEquationTCStatement`](CuspidalPairFunctionalEquationTCStatement.md);
* the theorem `cuspidalPairPartialGammaTCReduction`, which proves
  `CuspidalPairPartialGammaTCReductionStatement`;
* two restriction lemmas. `cuspidalPairPartialGammaEquationTC_of_partialGamma` says that (G')
  implies its TC form. `cuspidalPairCompletedEquationTC_of_completedEquation` says that
  `CuspidalPairCompletedEquationStatement` implies its TC form. Both proofs forget the instance:
  `fun F _ _ _ _ => h F`.

**The TC form of (G').** As its Markdown explains, it is the published (G') with the instance
argument `[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at the same
universes, the rest of the body verbatim. Its source is that of (G'): J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004) (`cogdell-2004-analytic-theory-gln`), proof
of Theorem 4.1, printed p.220 (PDF p.223). There the partial functional equation of
`L^S(s, π × π')` with the local gamma factors at the finite places of `S` is derived for every
number field. §1 of [`CuspidalPairPartialGammaReduction`](CuspidalPairPartialGammaReduction.md)
explains how (G') renders it. Restricting to TC fields is a specialization, not a change of
content.

**Why the TC form.** The Library's route to the local
correspondence applies the global functional equation only over the CM base field produced by
the globalization of Henniart (2000) §3 and over its finite extensions. These fields are all
totally complex. The Library states TC forms of the statements on that route, including
`CuspidalPairCompletedEquationTCStatement` (`CuspidalPairFunctionalEquationTCStatement.md` §4).
This module reduces it to the TC form of (G'), whose only archimedean input is at complex
places.

**What the TC restriction does.** By Mathlib's definition, `NumberField.IsTotallyComplex F`
means that every infinite place of `F` is complex. So the subtype
`{v : InfinitePlace F // v.IsReal}` is empty. In both TC statements:

* the hypotheses quantified over real places (`aR`, `dR`, `dR'`, `dRd`, `dRd'` and their
  specifications) are vacuous;
* the products over real places in `infiniteL`, `dualInfiniteL` and `infiniteEpsilon` are
  empty products, equal to `1`.

The complex-place factors are kept unchanged.

**Provenance of the reduction (internal).** Splitting the TC target at the TC form of (G') is
ours. It mirrors the published unrestricted chain:

```
cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma :
  CuspidalSatakeBoundStatement → CuspidalPairPartialGammaEquationStatement →
    CuspidalPairCompletedEquationStatement
```

That chain is stated for all number fields at once, so it does not give the TC form from the TC
premise. The proof here therefore repeats it one field at a time.

## 2. Statements

The imported premise `CuspidalPairPartialGammaEquationTCStatement.{u, uQ}` quantifies over
every number field `F : Type u` that is totally complex and has compact adele quotient. For
each such `F`, it quantifies over the data of (G'):

* a nontrivial unitary additive character `ψ` of the adeles, trivial on `F`;
* cuspidal realizations `T`, `Td` of `GL_(r+1)` and `T'`, `Td'` of `GL_(t+1)`, with `Td`, `Td'`
  the actual contragredients of `T`, `T'`;
* spectral presentations `P`, `P'`, `Pd`, `Pd'` with irreducible admissible components;
* a finite set `S` of finite places containing the four exceptional sets and supporting the
  finite ramification of `ψ`;
* additive components and archimedean parameters at the infinite places.

Its conclusion is that of (G'). There are a real `σ` and functions `Λ`, `Λd`, meromorphic on
`ℂ`, with the following properties.

* For `Re s > σ`, whenever the Euler product of the unramified factors outside `S` converges
  to `p`, `Λ(s) = L_∞(s) p`. Likewise `Λd(s) = L∨_∞(s) pd` for the contragredient pair.
* Take any canonical components `ψ_v` of `ψ`, any self-dual measures `ν_v`, and any rational
  functions `G_v` that are integral gamma factors of the actual local components at the places
  `v ∈ S`. Then, off a discrete set,
  `Λ(s) = (∏_(v ∈ S) G_v(q_v^(-s))) ε_∞(s) Λd(1 - s)`.

`CuspidalPairCompletedEquationTCStatement.{u, uQ}` is imported unchanged from
`CuspidalPairFunctionalEquationTCStatement` (see its Markdown). For the same data, together with every finite factor choice `c` unramified
outside `S`, it asserts `c.CompletedEquationHolds S L_∞ L∨_∞ ε_∞`.

## 3. The proof

`cuspidalPairPartialGammaTCReduction` introduces the TC premise `hG` and all data of the TC
target. In particular this includes the TC instance and a finite factor choice `c` with
`hc : c.IsUnramifiedOutside S`. The proof then takes three steps.

1. **Satake bounds.** `CuspidalSatakeBoundStatement.{u, uQ}` is proved in the Library as
   `cuspidalSatakeBoundReduction OperatorRealization.irreducibleCentralCharacter`. These are
   modules `CuspidalSatakeBoundReduction` and
   `Langlands.Automorphic.IrreducibleCentralCharacterProof`. It holds for every number field,
   hence for `F`. Applying it to `P`, `P'`, `Pd`, `Pd'` gives reals `A`, `B`, `Ad`, `Bd` with
   `HasSatakeBound P A` and so on.
2. **Continuation.** `hG` at `F` gives `σ`, `Λ`, `Λd` and the four conjuncts. The published
   per-field lemma `FinitePairFactorChoice.continuationHolds_of_partialGamma` turns them into
   `c.ContinuationHolds S L_∞ L∨_∞ ε_∞`. Its arguments are exactly those used in the published
   `cuspidalPairPartialGammaReduction`:
   * the gamma functions `G_v` are the rational gamma expressions built from `c`'s ε-data and
     L-polynomials;
   * the gamma-factor hypothesis at `v ∈ S` is `c.isPadicSymmetricGammaFactor`;
   * the local comparison at `v ∈ S` is `c.eventually_finiteL_mul_gamma`;
   * the canonical additive components and self-dual measures are those carried by `c`.
3. **Completed equation.** The published per-field lemma
   `FinitePairFactorChoice.completedEquationHolds_of_continuationHolds` takes the four Satake
   bounds and the continuation and gives `c.CompletedEquationHolds S L_∞ L∨_∞ ε_∞`.

None of these steps uses the TC instance. It is carried only so that `hG` can be applied at
`F`.

A compilation of the module reported 0 errors and 0 warnings. The theorem
`cuspidalPairPartialGammaTCReduction` depends only on the axioms `propext`, `Classical.choice`
and `Quot.sound`.

## 4. Scope and the premise

* This is a reduction. It does not prove `CuspidalPairCompletedEquationTCStatement`. Its one
  premise, `CuspidalPairPartialGammaEquationTCStatement`, is not proved in the Library.
* By `cuspidalPairPartialGammaEquationTC_of_partialGamma`, a proof of the unrestricted (G')
  proves the TC premise. With this reduction it then proves the TC target. The
  unrestricted target also follows, by the published
  `cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma`.
* A proof of only the TC form of (G') needs the archimedean local functional equations at
  complex places only. `CuspidalPairPartialGammaGlobalTCReduction` derives it from global
  Rankin–Selberg statements with TC semilocal equations (see the premise's Markdown). With this
  reduction such a proof gives the TC target, but not the unrestricted
  `CuspidalPairCompletedEquationStatement`.
* This module gives no unconditional proof of the unrestricted
  `CuspidalPairCompletedEquationStatement`, and the Library does not prove it.
