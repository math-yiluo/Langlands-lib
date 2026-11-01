# Uniqueness of the chosen valuation on a finite local extension: statement

This module defines
`Langlands.NYLL.LocalFieldTheory.ChosenLocalExtensionUniqueValuationExtensionStatement.{y} : Prop`.
It restates the conclusion of NYLL M248.011 as a closed proposition by
expanding the uniqueness predicate M196.001. It supplies the statement
target; it supplies no proof of that proposition.

The entry module is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenUniquenessStatement`.
It imports the published [chosen-data module](Chosen.md) and
`Mathlib.RingTheory.Valuation.Extension`. The chosen-data module also supplies
the published [canonical base](Canonical.md). Both definitions are preserved.

## Complete telescope and universe scope

In namespace `Langlands.NYLL.LocalFieldTheory`, the definition is exactly:

```lean
universe y

def ChosenLocalExtensionUniqueValuationExtensionStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
      (v' : _root_.Valuation L Gamma')
      [_root_.Valuation.HasExtension (localCompleteDVF K).valuation v'],
      (chosenLocalExtensionCompleteDVF K L).valuation.IsEquiv v'
```

The declaration has no free mathematical parameters. Every displayed field,
instance, valuation and extension witness is quantified inside the proposition.
Its only universe parameter is `y`. Both field carriers are `Type 0`; the
canonical base and chosen target have complete-DVF package universes `0, 0`.
For each arbitrary universe `y`, the comparison group `Gamma'` ranges over
all linearly ordered commutative groups with zero in `Type y`.

The supplied `Algebra K L` is arbitrary, subject to its finite-dimensionality
and separability hypotheses. There is no proper-extension or positive-degree
restriction beyond those hypotheses, so the identity extension is included.
The supplied `ValuativeRel K`, topology and nonarchimedean-local-field
instance determine `localCompleteDVF K`. There is no independently supplied
valuation, topology or local-field instance on `L`. The upstairs valuation in
the conclusion is exactly the already published
`(chosenLocalExtensionCompleteDVF K L).valuation`.

## Extension and equivalence conventions

Mathlib's `Valuation.HasExtension vK v'` states
`vK.IsEquiv (v'.comap (algebraMap K L))`. Thus the displayed extension
hypothesis uses the actual algebra map from the supplied `Algebra K L`.
It allows equivalent normalizations on restriction. It does not require
equality of maps into a common value group.

Mathlib's `Valuation.IsEquiv v w` is the proposition
`∀ r s, v r ≤ v s ↔ w r ≤ w s`: the valuations induce the same preorder.
The conclusion uses that predicate with the named chosen valuation as its
first argument and the arbitrary comparison valuation as its second.
The two value groups may differ, including their universes.

The comparison valuation `v'` only needs the displayed valuation type and
`HasExtension` instance. Completeness, discreteness and nontriviality are
not additional hypotheses on `v'`.

The proposition has no extra premise asserting that the chosen valuation
extends the base. That fact is already supplied separately by
`chosenLocalExtension_properties`, whose exact target is
`ChosenLocalExtensionPropertiesStatement`; see
[the published properties proof](ChosenPropertiesProof.md).
No uniqueness, henselianity, integral-closure or finite-module certificate
has been added as an assumption here.

## Original-to-adapted declaration map

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The read-only source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Original declaration | Adaptation in this module |
| --- | --- |
| M248.011, `LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension`, lines 194–204 of `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean` | Its full field/algebra/local-base telescope and expanded conclusion become `Langlands.NYLL.LocalFieldTheory.ChosenLocalExtensionUniqueValuationExtensionStatement.{y}`. Its proof is omitted. |
| M196.001, `ValuationTheory.DiscreteValuationField.ValuedExtension.HasUniqueValuationExtension`, lines 33–37 of `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Uniqueness.lean` | Its body is expanded directly with `base := localCompleteDVF K`, `target := chosenLocalExtensionCompleteDVF K L`, and universes `0, 0, 0, 0, y`. No generic predicate is introduced. |
| M248.001, `LocalFieldTheory.localCompleteDVF` | Reused as the published `Langlands.NYLL.LocalFieldTheory.localCompleteDVF`. |
| M248.006, `LocalFieldTheory.chosenLocalExtensionCompleteDVF` | Reused as the published `Langlands.NYLL.LocalFieldTheory.chosenLocalExtensionCompleteDVF`. |

M196.001 universally quantifies over comparison valuations and extension
instances and concludes `target.valuation.IsEquiv v'`. The surrounding
source variables for finite-dimensionality and the chosen target's
`HasExtension` instance are unused by that definition. Expanding its body
therefore introduces neither as a new premise. Finite-dimensionality remains
in this target because it is part of M248.011's telescope and the published
chosen construction.

The source M248.011 proves the predicate using
`hasUniqueValuationExtension_of_finite_separable` (M196.021). That generic
theorem is not an available published proof input for this statement unit.
The present definition records its local specialization as a proposition;
it does not port that proof or the generic uniqueness chain.

## Attribution, modifications and source checks

The original copyright and author header is retained verbatim in the Lean
file: copyright 2026 Naganori Yamaguchi, author Naganori Yamaguchi
(assisted by OpenAI Codex), under Apache-2.0. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained unchanged.
Worker 106 specified the closed target telescope in the task; Worker 1199
prepared this statement adaptation and its documentation.

The explicit modifications are closing the source telescope inside a new
Prop-valued `def`, expanding M196.001 at the indicated universes, omitting
the source proof, prefixing the namespace with `Langlands.NYLL`, writing
`Valuation.HasExtension` in prefix form, and replacing the source imports
with the published chosen-data module and the focused Mathlib import.
The named canonical and chosen definitions are reused without edits.

The original source fingerprints are:

- M248, `FiniteExtensionCompleteDVF.lean`:
  `f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.
- M196, `FiniteExtension/Uniqueness.lean`:
  `fb67f19f74a29be3d63ad92ce83a952da8f4ac54a07dc243793b578771656a29`.

Worker 1199 verified both complete-file hashes, read all 206 lines of M248,
and read M196 lines 1–118 and 576–618 for the predicate and generic theorem.
The registered source records are
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.
The [M248 partition](../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m248)
and [M196 partition](../../../../../../notes/reuse/nyll-public-port/m193-m216.md#m196)
record no patch10 compatibility edit for these modules. No applicable
errata file was found among the current Library or project notes.

The adaptation uses the approved Lean 4.34.0 environment with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; the upstream pins are Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Scope

This unit publishes only the closed uniqueness proposition. Its exact-target
proof is separate, as are generic uniqueness declarations, new global
instances, M248.003/.004 canonical integer-ring comparisons and host
reciprocity adapters. It makes no assertion of arbitrary-universe field
carriers or reciprocity.
