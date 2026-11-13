# NYLL M110.009: the actual integral closure as a valuation subring

The pinned original is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`.
The readable source is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean`.
The exact Lean file SHA-256 is
`8f2d21dcbef11b6354d840a350ea2ddf775b670d74581bf9469d499afbe34dad`.
The registered source is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
the source snapshot is also recorded by
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Copyright 2026 Naganori Yamaguchi; original authors Naganori Yamaguchi
(assisted by OpenAI Codex). The source header is retained in the Lean file.
The unchanged upstream license and notices are in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 194 extracted and namespaced this unit on 13 November 2026.

The source context is at lines 21-33: namespace
`ValuationTheory.DiscreteValuationField.Valuation`, a noncomputable section,
universes `u v w x y z`, then
`{K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]`,
`{ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]`.
The port retains that context in the same order. Lean generalizes the used
section parameters and retains all declaration-local binders. Unused source
universe names are not artificial extra universe parameters on declarations.

The exact original-to-adapted map is
`ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv`
(source lines 222-230, source doc comment at 215-221) to
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv`.

For a valuation `vK` on `K`, this constructs a `ValuationSubring L` from the
actual subring `(integralClosure vK.valuationSubring L).toSubring` and the
supplied hypothesis `hval`: every `z : L` or its inverse belongs to that subring.
The complete explicit binders are `(vK : _root_.Valuation K ΓK)` followed by
`(hval : ∀ z : L, z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)`.
The value is exactly
`ValuationSubring.ofSubring (integralClosure vK.valuationSubring L).toSubring hval`.
There is no choice of another subring or assumption of Henselianity,
discreteness, algebraicity, or finite dimensionality.

The original imports through NYLL's `ValuationExtension` are replaced by
focused Mathlib imports. No requested statement uses the upstream DVF packages,
residue-field namespace, or any unpublished declaration from another NYLL
module, so those dependencies and the unused `open` command are omitted.
Mathlib supplies the actual valuation subrings, canonical valuations,
`Valuation.HasExtension`, algebras, local rings, ideals and scalar towers.
No global instance or axiom is introduced. The namespace is prefixed by
`Langlands.NYLL`; the source spelling of `_root_.Valuation` is retained to
avoid resolving it to the source's `Valuation` namespace.

This file imports only `Mathlib.RingTheory.DedekindDomain.IntegralClosure`
and `Mathlib.RingTheory.Valuation.ValuationSubring`. The body, all parameters,
binder kinds, universes and supplied proof argument are unchanged from M110.009.
Only the namespace, imports and explanatory comments change. The surrounding
noncomputable section remains; the definition installs no instance.
The construction directly reuses Mathlib's `ValuationSubring.ofSubring`;
Mathlib's canonical subring, field and valuation structures are not copied.

Theorem properties of this construction are separate proposition targets in
`IntegralClosureValuationSubringStatements.lean`. This definition does not
assert or prove the supplied valuative dichotomy for any particular extension.
The environment for focused checks is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
