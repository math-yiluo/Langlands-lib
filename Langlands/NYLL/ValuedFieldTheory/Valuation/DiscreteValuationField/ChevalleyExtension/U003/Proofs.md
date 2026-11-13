# Chevalley's extension theorem in valuation-subring form (NYLL M110.003)

This module proves the published proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubringStatement`
by the theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring`.
Its sole import is the statement module
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements`,
which is left unchanged.

## Target and mathematical meaning

The theorem has implicit fields `K : Type u`, `L : Type v` with
`[Field K] [Field L] [Algebra K L]`, implicit `ΓK : Type w` with
`[LinearOrderedCommGroupWithZero ΓK]`, and explicit `vK : Valuation K ΓK`.
Its type is `exists_extension_valuationSubringStatement (L := L) vK`, which
unfolds to

```lean
∃ B : ValuationSubring L,
  ∃ hB : ∀ x : vK.valuationSubring, algebraMap vK.valuationSubring L x ∈ B.toSubring,
    IsLocalHom ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB) ∧
    ∀ x : K, algebraMap K L x ∈ B.toSubring ↔ x ∈ vK.valuationSubring
```

Mathematically (Chevalley's extension theorem): for every field extension
`L / K` (no algebraicity or finiteness is assumed) and every valuation `vK` on
`K` with valuation ring `O_v`, there is a valuation ring `B` of `L` that
contains the image of `O_v`, such that `O_v → B` is a local homomorphism, and
such that `B ∩ K = O_v`.

## Implemented proof

After `unfold exists_extension_valuationSubringStatement` the rest is the source
tactic proof. Mathlib's `IsLocalRing.exists_factor_valuationRing`
(`Mathlib/RingTheory/Valuation/LocalSubring.lean`), applied to the algebra map
`vK.valuationSubring →+* L` from the local ring `vK.valuationSubring`, supplies
`B`, `hB` and the locality `hlocal`. For the pullback equivalence:

* if `algebraMap K L x ∈ B`, the private theorem
  `mem_base_valuationSubring_of_lift_mem_aux vK B hB hlocal hxB` gives
  `x ∈ vK.valuationSubring`;
* if `x ∈ vK.valuationSubring`, then `hB ⟨x, hxA⟩` says the image of
  `⟨x, hxA⟩` lies in `B`; rewriting with
  `IsScalarTower.algebraMap_apply vK.valuationSubring K L` and `simpa` turns it
  into `algebraMap K L x ∈ B.toSubring`.

The private theorem `mem_base_valuationSubring_of_lift_mem_aux` is a local copy
of the source proof of M110.002 (source lines 47–76, byte-identical tactic
script), with the source conclusion `x ∈ vK.valuationSubring` as its type:
`ValuationSubring.mem_or_inv_mem` splits into `x ∈ O_v` or `x⁻¹ ∈ O_v`; in the
second case with `x ≠ 0`, the image of `x` in `B` inverts the image of `x⁻¹`,
so locality (`IsUnit.of_map`) makes `x⁻¹` a unit of `O_v`, whence its
valuation and that of `x` equal one and `x ∈ O_v`. The task contract asks not
to import unpublished proofs and not to publish a second copy of the M110.002
theorem under its adapted name; the copy is therefore `private` and named
differently, and the public M110.002 theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.mem_base_valuationSubring_of_lift_mem`
is staged separately in `ChevalleyExtension/U002/Proofs.lean`.

Dependencies are Mathlib only (`IsLocalRing.exists_factor_valuationRing`,
`IsScalarTower.algebraMap_apply`, the `ValuationSubring` API and unit lemmas),
all available through the statement module's imports. No public auxiliary
declaration, instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean:86–109`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean#L86-L109)
(partition unit lines 86–112; docstring at lines 78–85; the M110.002 proof
copied privately is at lines 47–76).

| Original (namespace `ValuationTheory.DiscreteValuationField.Valuation`) | Adapted |
| --- | --- |
| Theorem `exists_extension_valuationSubring`, lines 86–109 | This theorem, same name under `Langlands.NYLL.` |
| Conclusion, lines 88–94 | `exists_extension_valuationSubringStatement (L := L) vK` |
| Tactic proof, lines 95–109 | Identical after one `unfold`, except that the call at line 102 names the private copy |
| Theorem `mem_base_valuationSubring_of_lift_mem`, lines 47–76 | Private `mem_base_valuationSubring_of_lift_mem_aux` with the identical type telescope and tactic script |

Other adaptations: the `Langlands.NYLL` namespace prefix; the single statement
import in place of the source imports; omission of the unused universes
`x y z`, the `noncomputable section` and the unused `ResidueField` open.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 133's dated modification record. Worker 133 extracted
this proof directly from the pinned original and the frozen statement module;
there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The whole source file has SHA-256
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`, recomputed by
Worker 133 on 13 November 2026 UTC. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m110)
lists this unit in module M110 (no patch10 edit applies).

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), where the module
compiles with no errors or warnings and the theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. Compilation is not acceptance:
publication under `lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
