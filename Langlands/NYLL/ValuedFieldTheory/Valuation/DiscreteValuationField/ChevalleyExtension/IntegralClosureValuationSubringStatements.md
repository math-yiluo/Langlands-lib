# NYLL M110: properties of the constructed integral-closure subring

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

| Unit | Original declaration | Signature lines | Full source command | Adapted declaration |
| --- | --- | --- | --- | --- |
| M110.010 | `ValuationTheory.DiscreteValuationField.Valuation.mem_integralClosureValuationSubringOfMemOrInv` | 233-241 | 233-242 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.mem_integralClosureValuationSubringOfMemOrInvStatement` |
| M110.011 | `ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_pullback` | 246-255 | 246-257 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_pullbackStatement` |
| M110.012 | `ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension` | 262-269 | 262-272 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_hasExtensionStatement` |
| M110.013 | `ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosure` | 282-291 | 282-310 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosureStatement` |
| M110.014 | `ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension` | 314-323 | 314-331 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtensionStatement` |

- `mem_integralClosureValuationSubringOfMemOrInvStatement`: Membership in the constructed valuation subring is precisely membership in the actual integral closure.
- `integralClosureValuationSubringOfMemOrInv_pullbackStatement`: The constructed valuation subring has exact pullback to the base valuation ring.
- `integralClosureValuationSubringOfMemOrInv_hasExtensionStatement`: The canonical valuation of the constructed subring extends the base valuation.
- `integralClosureValuationSubringOfMemOrInv_isIntegralClosureStatement`: The constructed subring satisfies IsIntegralClosure for the actual field extension.
- `integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtensionStatement`: The constructed subring is contained in every extending valuation ring.

Each adapted declaration is a `def` returning `Prop`, with precisely the
source theorem's generalizing section parameters and declaration-local binder
order and kinds. Its body is the source conclusion; its theorem proof is
omitted. Source hypotheses remain arguments of the definition, including named
proof arguments that do not occur in the conclusion. No `simp` attribute is
transferred to a proposition definition. The declarations specify proof targets;
this file publishes no proofs of those targets.

The original imports through NYLL's `ValuationExtension` are replaced by
focused Mathlib imports. No requested statement uses the upstream DVF packages,
residue-field namespace, or any unpublished declaration from another NYLL
module, so those dependencies and the unused `open` command are omitted.
Mathlib supplies the actual valuation subrings, canonical valuations,
`Valuation.HasExtension`, algebras, local rings, ideals and scalar towers.
No global instance or axiom is introduced. The namespace is prefixed by
`Langlands.NYLL`; the source spelling of `_root_.Valuation` is retained to
avoid resolving it to the source's `Valuation` namespace.

The imports are `Mathlib.RingTheory.Valuation.Extension`,
`Mathlib.RingTheory.DedekindDomain.IntegralClosure` and the paired construction
module `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.Definitions`.
Every construction occurrence uses the exact namespaced M110.009 definition.
The explicit `vK` and `hval` binders remain in source order; M110.010 also has
`z : L`, M110.011 has `a : K`, and M110.014 retains its independent
`{ΓL : Type x}` and instance, then `vK`, `vL`, `hval`, and the extension
instance in precisely that order.

M110.013's original conclusion reads, after the same binders:

```lean
let B := integralClosureValuationSubringOfMemOrInv (L := L) vK hval
letI : vK.HasExtension B.valuation :=
  integralClosureValuationSubringOfMemOrInv_hasExtension (L := L) vK hval
IsIntegralClosure B vK.valuationSubring L
```

The target retains `let B` and zeta-erases only the unused `letI` proof
binding. Mathlib's `IsIntegralClosure B A L` requires `[Algebra A L]` and
`[Algebra B L]`, not `[Algebra A B]`, and its elaborated conclusion contains
no use of that `HasExtension` instance. Thus the resulting proposition is
definitionally equal to the source conclusion and has no extra hypothesis.
This normalization avoids requiring an unpublished proof of M110.012 while
stating M110.013. A private focused `rfl` comparison checks the source-form
conclusion with an arbitrary proof occupying that unused let binding; its
value cannot affect the equality. All other conclusions are copied unchanged.
In addition to that single normalization, the only changes are namespace,
focused imports, explanatory comments, and replacing theorem/proof by
proposition body. M110.010's source `simp` attribute is not put on the new def.

The environment for focused checks is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
The full closed declaration functions are compared definitionally in a private
source-signature check, and each target is separately inspected as returning
`Prop`. Compilation and inspection are development checks; these targets
retain independent semantic review and separate future proof obligations.
None asserts a host reciprocity, class-formation, cup, transfer or Tate result.
