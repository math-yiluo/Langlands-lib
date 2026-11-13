# Inverting the horizontal isomorphisms of a commutative square: statement

This module defines one closed proposition,
`Langlands.NYLL.PortInternal.M086.d018Statement : Prop`, the statement phase
of source row M086.018, the private theorem
`ClassFormation.normResidueNaturality_symm_naturality`. The module contains
no proof. A separate proof child will prove it under the name
`Langlands.NYLL.PortInternal.M086.d018`. The source theorem is `private`,
so, as for other private NYLL theorems in the Library, it is named by its
source row in the namespace `Langlands.NYLL.PortInternal.M086`.

## Complete closed telescope

The definition has four universe parameters `u₁ u₂ u₃ u₄` (the source's
four `Type*` binders) and no other parameters. Its body is

```lean
∀ {Q : Type u₁} {B : Type u₂} {Q' : Type u₃} {B' : Type u₄}
  [AddCommGroup Q] [AddCommGroup B]
  [AddCommGroup Q'] [AddCommGroup B']
  (r : Q ≃+ B) (r' : Q' ≃+ B')
  (q : Q →+ Q') (b : B →+ B'),
  b.comp r.toAddMonoidHom = r'.toAddMonoidHom.comp q →
    q.comp r.symm.toAddMonoidHom =
      r'.symm.toAddMonoidHom.comp b
```

The binders are those of the source theorem, in the same order and with
the same binder kinds. The source names the commutativity hypothesis `h`;
the conclusion does not mention it, so it is an anonymous premise here. The
source's section variables `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]` (line 1000) are not mentioned by the theorem and are
not part of its telescope.

## Meaning

Given abelian groups `Q, B, Q', B'`, additive isomorphisms `r : Q ≃ B` and
`r' : Q' ≃ B'`, and additive homomorphisms `q : Q → Q'`, `b : B → B'` such
that the square commutes, `b ∘ r = r' ∘ q`, the square with the horizontal
isomorphisms inverted also commutes: `q ∘ r⁻¹ = r'⁻¹ ∘ b` as homomorphisms
`B → Q'`. The source uses it to turn reciprocity squares into the
naturality diagrams for the inverse norm-residue symbol (M086.029 and
M086.030).

## Reused declarations

Only Mathlib is used: `AddCommGroup`, `AddEquiv` (`≃+`, `symm`,
`toAddMonoidHom`) and `AddMonoidHom` (`→+`, `comp`). The single import
`Mathlib.Algebra.Group.Equiv.Defs` provides them.

## Library search

The whole Library at commit `ccda47ce0341746db208ee15e862d9226cc25fcc` was
searched for `symm_naturality`, for compositions with
`.symm.toAddMonoidHom`, and for the namespace `PortInternal.M086`. The existing
`symm_naturality` lemmas concern specialized comparisons, including affinoid
spectra, sheaf cohomology and the Renard cone comparison. The namespace
`PortInternal.M086` does not exist at that commit. No declaration states this
square lemma for additive isomorphisms. So nothing in the Library already
covers M086.018. Worker 5264 (Task 5264, M258 closure) confirmed that
M086.014–M086.031 are outside that closure and may be published by
Task 5799.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean>),
SHA-256 `6883a1db96a9baf23b9c4f040e635f10b7732f36c558d9e0a96faa88a2da854b`.
The header is at lines 1–5, the namespace `ClassFormation` at 26 and the
second `noncomputable section` with its `variable` line at 997 and 1000.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M086.018, private `ClassFormation.normResidueNaturality_symm_naturality` | docstring 1002–1003, signature 1004–1013, proof 1014–1022 (omitted) | `Langlands.NYLL.PortInternal.M086.d018Statement` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted type directly from the pinned original on
13 November 2026 and made these changes:

- The private theorem becomes the Prop-valued definition `d018Statement` in
  `Langlands.NYLL.PortInternal.M086`, named after its source row. All binders
  move inside the proposition in the same order and with the same binder
  kinds; the four `Type*` binders get the explicit universes `u₁ u₂ u₃ u₄`.
  The hypothesis `h` becomes an anonymous premise. The proof is omitted for
  the separate proof phase.
- The docstring is adapted from the source docstring to name the source
  theorem and row.
- The source imports are replaced by `Mathlib.Algebra.Group.Equiv.Defs`.
- All other declarations of the source file are omitted.

No instance or simp attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this statement. Its truth proof belongs to a
separate proof unit published after the statement is accepted.
