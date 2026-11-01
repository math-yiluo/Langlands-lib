# Uniqueness of the chosen valuation on a finite local extension: proof

This module proves the published closed target
`Langlands.NYLL.LocalFieldTheory.ChosenLocalExtensionUniqueValuationExtensionStatement.{y}`.
Its sole theorem is
`Langlands.NYLL.LocalFieldTheory.chosenLocalExtension_uniqueValuationExtension`,
in entry module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenUniquenessProof`.
The entire theorem type is exactly that proposition:

```lean
universe y

theorem chosenLocalExtension_uniqueValuationExtension :
    ChosenLocalExtensionUniqueValuationExtensionStatement.{y}
```

The [published statement pair](ChosenUniquenessStatement.md) and its imported
definitions are unchanged. Both field carriers are `Type 0`. There are no free
mathematical arguments and the theorem's only universe parameter is `y`.

## Target and conventions

The proposition internally quantifies over `K L : Type`, their `Field`
instances, the supplied `Algebra K L`, `FiniteDimensional K L`,
`Algebra.IsSeparable K L`, and the supplied `ValuativeRel K`,
`TopologicalSpace K` and `IsNonarchimedeanLocalField K`. For every
`Gamma' : Type y` with `LinearOrderedCommGroupWithZero Gamma'`, and every
`v' : Valuation L Gamma'` with
`Valuation.HasExtension (localCompleteDVF K).valuation v'`, it proves
`(chosenLocalExtensionCompleteDVF K L).valuation.IsEquiv v'`.
The identity extension is included.

Mathlib's `HasExtension` means equivalence of the base valuation with the
comparison valuation pulled back along the actual supplied `algebraMap K L`.
It permits equivalent normalizations. `IsEquiv` means that, for every `r s`,
the two inequalities `v r ≤ v s` and `w r ≤ w s` are equivalent. Here the
named chosen valuation is the first argument and the arbitrary comparison
valuation is the second. The comparison valuation needs no completeness,
discreteness or rank-one instance.

## Implemented proof

Write `vK := (localCompleteDVF K).valuation` and
`vL := (chosenLocalExtensionCompleteDVF K L).valuation`.
The proof introduces the entire telescope of the target, then specializes the
accepted [chosen properties theorem](ChosenPropertiesProof.md).
It obtains `hExt : Valuation.HasExtension vK vL`, the assertion that
`vL.valuationSubring` is the integral closure of `vK.valuationSubring` in `L`,
and its module-finiteness assertion. The first two are installed as local
instances with anonymous `let` bindings; module-finiteness is not needed in
this proof. No global instance is added.

Mathlib's `Valuation.isEquiv_iff_valuationSubring` reduces the goal to equality
of the two valuation subrings. The stored complete-discrete valuation on the
chosen package supplies rank-one discreteness, hence the DVR instance on its
valuation subring. The existing principal-ideal/Dedekind-domain instances
supply `Ring.KrullDimLE 1` for that ring.
The proof applies `ValuationSubring.eq_of_le_of_ne_top`, which says that an
overring of such a valuation ring equals it if the overring is not the whole
field. Its two obligations are discharged as follows.

1. For `z ∈ vL.valuationSubring`, the local `IsIntegralClosure` instance and
   `IsIntegralClosure.isIntegral_iff` give integrality of `z` over
   `vK.valuationSubring`. The comparison `HasExtension` instance supplies the
   algebra from that base ring to `v'.valuationSubring` and the compatible
   scalar tower into `L`. `IsIntegral.tower_top` therefore makes `z` integral
   over `v'.valuationSubring`. Applying
   `Valuation.Integers.mem_of_integral` to
   `Valuation.valuationSubring.integers v'` gives
   `z ∈ v'.valuationSubring`. This proves the required containment.
2. The stored rank-one discreteness of `vK` supplies nontriviality, so
   `Valuation.IsNontrivial.exists_one_lt` provides `a : K` with `1 < vK a`.
   If `v'.valuationSubring = ⊤`, then `v' (algebraMap K L a) ≤ 1`.
   `Valuation.HasExtension.val_map_le_one_iff` converts this to `vK a ≤ 1`,
   contradicting the chosen strict inequality.

Thus the subrings are equal, and the initial equivalence criterion proves the
required `IsEquiv`. All comparisons occur in valuation rings inside `L`;
the proof never identifies the two value groups, so it retains arbitrary `y`.
Completeness and separability enter through the already published construction
and properties of the chosen package. There is no additional uniqueness or
integral-closure premise in the theorem.

## Source correspondence and attribution

The mathematical source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Correspondence |
| --- | --- |
| M248.011, `LocalFieldTheory.chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension`, lines 194–204 of `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean` | The theorem proves its closed local specialization, exactly as recorded in the published target. |
| M196.001, `ValuationTheory.DiscreteValuationField.ValuedExtension.HasUniqueValuationExtension`, lines 33–37 of `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteExtension/Uniqueness.lean` | The published target expands this predicate at universes `0, 0, 0, 0, y`. |
| M196.011, `hasUniqueValuationExtension_of_target_valuationSubring_isIntegralClosure`, lines 384–398 | The source also isolates the integral-closure criterion. The implemented proof uses Mathlib's dimension-one overring theorem directly after obtaining that criterion from the accepted chosen properties. |
| M196.021, `hasUniqueValuationExtension_of_finite_separable`, lines 594–612 | The source M248.011 invokes this generic Henselian/integral-closure chain. This implementation does not import or assume that unpublished generic theorem. |

Worker 1199 read all 206 lines of M248 and M196 lines 1–118, 360–428 and
576–618, and verified the complete source-file hashes:
M248 `f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`;
M196 `fb67f19f74a29be3d63ad92ce83a952da8f4ac54a07dc243793b578771656a29`.
The published partition records no patch10 edit for these modules.
No applicable errata file was found in the current Library or project notes.

The original copyright and author header is retained verbatim: copyright 2026
Naganori Yamaguchi, author Naganori Yamaguchi (assisted by OpenAI Codex),
under Apache-2.0. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged. Worker 106 supplied the exact closed
target specification; Worker 1199 implemented and documented this direct proof.
The explicit modification notice records the changed proof route, local
instance installation, namespace prefix and focused imports.

This proof uses the approved Lean 4.34.0 environment with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The upstream pins were Lean
4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Scope

The result is chosen-valuation uniqueness for the exact published Type 0
field telescope and arbitrary comparison value-group universe. Generic
uniqueness, independently supplied upstairs structures, canonical integer-ring
comparisons, host reciprocity, arbitrary-universe field carriers and
cohomological agreement remain separate.
