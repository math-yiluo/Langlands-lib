# Renard VI.7.2 Proposition from five named statements

Worker 76. Supporting reduction for proof task
`2a804ec7-6b5f-4bbe-93ab-39527f9b50a9` (Renard VI.7.2 Proposition,
`Langlands.CuspidalSupport.BernsteinBlockCharacterizationStatement`). This
module proves the characterization of a Bernstein block **conditionally** on
five published propositions. None of them is proved yet, and none is proved here:

| hypothesis | published proposition | source | proof task |
|---|---|---|---|
| `hSplit` | `RationalCuspidalInertiaDecompositionStatement.{uF, max uF uV}` | VI.3.3.1 | `5c59bed4-0f33-47e1-aaa6-1d1145b8b25f` |
| `hwhole` | `RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}` | VI.3.5 | `4bee987a-093b-4054-bd65-7360168351d2` |
| `hind` | `RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV}` | VI.5.2 | `fc21c11d-1a31-468d-a90e-fdda36098677` |
| `hJF` | `BernsteinBlockJacquetFaithfulStatement.{uF, uV}` | VI.10.3 | `2174cd68-b110-4f86-b992-28712c29d35f` |
| `hProg` | `RationalSummandSmallProgeneratorStatement.{uF, max uF uV}` | VI.4.1 | `ca5fea74-6ce4-457c-9947-4427cbfdbdd8` |

The first two names and the last three are in namespace
`Langlands.CuspidalSupport`; `RepresentedParabolic` is
`Langlands.Aubert.General.RepresentedParabolic`. When all five have published
proofs, applying `bernsteinBlockCharacterization_of_statements` to them gives an
unconditional theorem whose type is exactly the target.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The target is VI.7.2, Proposition, printed p.184 / PDF p.190, with its proof on
printed pp.184–185 / PDF pp.190–191. The inputs are at these places:
VI.3.3.1, printed p.145 / PDF p.151; VI.3.5, printed pp.146–147 / PDF
pp.152–153; VI.5.2, printed p.173 / PDF p.179; VI.10.3, printed p.209 / PDF
p.215; VI.4.1, printed p.149 / PDF p.155.

## Provenance

No source states this implication. It is derived. It is the composition of
published reductions and adds no mathematics of its own. The route differs from
the printed proof of (i) in one place. To embed `V` in an induction from the
fixed standard Levi `M`, the published reduction uses VI.10.3, the Levi
decomposition VI.3.3.1 and first adjointness, `V ↪ i_P(r_P(V)_D)`. It does not
rewrite an induction `i_Q(τ')` from a conjugate pair `(L, D')` as an induction
from `(M, D)`; the printed proof makes that rewrite without justification. The
published modules below give the details.

## Declarations

- `bernsteinBlockCharacterizationLeviInputs_of_statements (hSplit hwhole hind)`
  proves `BernsteinBlockCharacterizationLeviInputs.{uF, uV}`. This proposition
  is stated in
  `Langlands.Representation.CuspidalSupport.BernsteinFixedLeviEmbeddingReduction`.
  It asks, for every nonarchimedean local field, actual connected group scheme
  data and Bernstein standard family, for two per-family facts.
  - The Levi block projection `BernsteinLeviBlockProjection`. It is supplied by
    `bernsteinLeviBlockProjectionOfRationalInertiaDecomposition … hSplit`
    (module `BernsteinLeviInertiaProjection`), which takes VI.3.3.1 to the
    actual standard Levi of each cuspidal datum and projects onto the
    datum's inertia block.
  - The geometric exclusion `BernsteinInducedInertiaJacquetExclusion`. It is
    supplied by `bernsteinInducedInertiaJacquetExclusion_of_supercuspidal …
    hwhole` (module `BernsteinDecompositionInputsAssembly`). VI.3.5 makes every
    object of the same-Levi inertia block supercuspidal, which reduces the
    exclusion to supercuspidal inducing objects. That case is
    `bernsteinJacquetExclusionOfInertiaBlockSupercuspidal … hind` (module
    `BernsteinInducedInertiaGeometricExclusion`): the conjugate-Levi case uses
    the published VI.5.3 (iii) filtration, and the nonconjugate case uses
    VI.5.3 (ii), whose reduction uses VI.5.2.
- `bernsteinBlockCharacterization_of_statements (hSplit hwhole hind hJF hProg)`
  proves `BernsteinBlockCharacterizationStatement.{uF, uV}`. The proof applies
  `bernsteinBlockCharacterization_of_leviInputs` (module
  `BernsteinFixedLeviEmbeddingReduction`) to the previous result, VI.10.3 and
  VI.4.1. That theorem builds the fixed-Levi embedding from the projection and
  VI.10.3, using VI.4.1 to place the summand progenerator `Π_D` in the Levi
  block. It then applies the published
  `bernsteinBlockCharacterization_of_embedding_and_exclusion`.
- `bernsteinBlockCharacterizationOfStatements` is a definition whose type is the
  same implication, written as a chain of five arrows, and whose value is the
  theorem above. The linter `linter.defProp` is switched off for this one
  declaration.

## Universes

The target is at `uF, uV`, with representation carriers in `max uF uV`. The
inputs VI.3.3.1, VI.3.5, VI.5.2 and VI.4.1 are used at carrier universe
`max uF uV`, because they are applied to representations of Levi subgroups whose
carriers lie in `max uF uV`. VI.10.3 is at `uF, uV`, like the target. These
are the universe arguments that the published reductions require. No universe
is fixed to a particular value, and the field universe `uF` and carrier universe
`uV` stay independent.

## Scope

This module does not prove the target unconditionally and does not discharge
any of the five hypotheses. Nothing beyond the five displayed propositions is
assumed. Every result keeps the published objects: the actual Bernstein cuspidal
data and blocks, the inertia relation, normalized induction and Jacquet
functors, arbitrary nonarchimedean local fields, including positive
characteristic, and all smooth representations.
