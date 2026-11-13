# Abelianization of an isomorphism onto a commutative group: proof

`Langlands.NYLL.PortInternal.M260.d006` proves the published target
`Langlands.NYLL.PortInternal.M260.d006Statement` for every choice of its
parameters:

```lean
theorem d006
    {G H : Type*} [Group G] [CommGroup H]
    (q : G ≃* H) (x : G) :
    d006Statement q x
```

So for a group isomorphism `q : G ≃* H` onto a commutative group,
`(Abelianization.equivOfComm (H := H)).symm (q.abelianizationCongr (Abelianization.of x)) = q x`.
Like the target, the theorem has the two universe parameters of `G` and `H`.

## Proof

The proof is the source proof term, unchanged. Mathlib's
`abelianizationCongr_of q x` says
`q.abelianizationCongr (Abelianization.of x) = Abelianization.of (q x)`; applying
`(Abelianization.equivOfComm (H := H)).symm` to both sides (`congrArg`) turns the
left side of the goal into `equivOfComm.symm (Abelianization.of (q x))`. Since
`equivOfComm` sends `h` to `Abelianization.of h`,
`(Abelianization.equivOfComm (H := H)).symm_apply_apply (q x)` identifies this with
`q x`. `Eq.trans` chains the two equalities.

## Source and modifications

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntermediateFieldNormResidueNaturality.lean`
(SHA-256 `0198546411975a802c5ea2441572ced6b9a7fcfa28a7a23a7bfdbf5e806a9ffb`),
private theorem `LocalClassFieldTheory.commGroup_abelianizationCongr_of` at lines
140–149 (inventory M260.006). The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `commGroup_abelianizationCongr_of` (private, M260.006) | `Langlands.NYLL.PortInternal.M260.d006` |

Modifications: only the source theorem is extracted; the private theorem becomes the public
`Langlands.NYLL.PortInternal.M260.d006`, following the port's naming rule for
private source commands; the conclusion is written as the published target
applied to the telescope; the only import is the statement module. The telescope
and proof term are unchanged. The source file's `noncomputable section` is
retained; its namespace openings and unused file-level universe and section
declarations are omitted. The source theorem has no docstring; the docstring is
the one of the published statement. As in the source, the enclosing section's
local-field variables are not mentioned and are not parameters.

The candidate compiled with zero errors and zero warnings in approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection of the named theorem
reports independent universe parameters `u_1, u_2` and only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. This development check is not
independent acceptance.

## Imports and scope

The sole direct import is the published target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntermediateFieldNormResidueNaturality.U006.Statements`.
It imports `Mathlib.GroupTheory.Abelianization.Defs`, which supplies the
abelianization definitions and the evaluation theorem used here. Compared with
the original source file, the direct Mathlib import is now obtained transitively;
the NYLL imports `IntrinsicAbsoluteData`, `Main` and
`IntermediateFieldRestriction`, and the Mathlib import
`Mathlib.FieldTheory.Galois.Abelian`, are omitted because this group-theoretic
helper uses none of their declarations. No external NYLL module is imported.
The published statement and everything it imports are used unchanged.

This proves only the stated group-theoretic identity; no reciprocity or
host-comparison result is asserted. Worker 293 reused Worker 89's complete
shared draft and added the dated preparation record and this import/scope
explanation, with no mathematical change.

## License

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted by
OpenAI Codex). It remains under Apache-2.0. The already-published `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` are reused unchanged and included through
`repository_paths`. Worker 89 adapted this proof directly from the pinned original;
Worker 293 prepared the candidate from that shared draft and verified it.
