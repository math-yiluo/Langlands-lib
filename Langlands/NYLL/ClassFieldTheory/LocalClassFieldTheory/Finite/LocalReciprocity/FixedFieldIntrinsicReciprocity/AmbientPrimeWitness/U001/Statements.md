# Transport of an identified abelianized prime value: statement

This module defines one closed proposition,
`Langlands.NYLL.LocalClassFieldTheory.abelianizationCongr_symm_eq_primeTargetStatement : Prop`.
It is the statement phase of source row M284.001, the theorem
`LocalClassFieldTheory.abelianizationCongr_symm_eq_primeTarget`. The module
contains no proof. A later proof child will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.abelianizationCongr_symm_eq_primeTarget`.

## Complete closed telescope

The definition has no parameters and no universe variables. Its entire body is

```lean
∀ {Q₀ G₀ G : Type}
  [Group Q₀] [Group G₀] [Group G]
  (q₀ : Q₀ ≃* G₀)
  (qE : Q₀ ≃* G)
  (qAmbient : Q₀)
  (r : Additive (Abelianization G₀)),
  r =
      Additive.ofMul
        (q₀.abelianizationCongr
          (Abelianization.of qAmbient)) →
  qE.abelianizationCongr
      (q₀.abelianizationCongr.symm
        (Additive.toMul r)) =
    qE.abelianizationCongr
      (Abelianization.of qAmbient)
```

The binders, in the source order, are:

| Binder | Kind and meaning |
| --- | --- |
| `{Q₀ G₀ G : Type}` | Implicit group types, in universe zero as in the source |
| `[Group Q₀]`, `[Group G₀]`, `[Group G]` | Instance-implicit group structures |
| `(q₀ : Q₀ ≃* G₀)` | Explicit group isomorphism |
| `(qE : Q₀ ≃* G)` | Explicit second group isomorphism with the same domain |
| `(qAmbient : Q₀)` | Explicit element of the common domain |
| `(r : Additive (Abelianization G₀))` | Explicit element of the abelianization of `G₀`, written additively |
| anonymous premise | The source hypothesis `hprime`, with the same type |

Every binder is quantified inside the proposition, with the source binder
kinds: the three group types stay implicit. The conclusion does not mention
the hypothesis, so its name `hprime` is dropped and the hypothesis becomes an
anonymous premise `… → …`. Its type is unchanged.

## Meaning

For a group isomorphism `e : A ≃* B`, Mathlib's
`MulEquiv.abelianizationCongr e : Abelianization A ≃* Abelianization B`
(`Mathlib/GroupTheory/Abelianization/Defs.lean`) is the induced isomorphism
of abelianizations. It sends the class `Abelianization.of a` to
`Abelianization.of (e a)`. `q₀.abelianizationCongr.symm` is its inverse.
`Additive.ofMul` and `Additive.toMul` only change the type tag between the
multiplicative group `Abelianization G₀` and its additive copy.

The premise says that the additive value `r` is the image of the class of
`qAmbient` under the abelianized `q₀`. The conclusion says that if one pulls
`r` back through the abelianized `q₀` and pushes it forward through the
abelianized `qE`, one gets the image of the class of `qAmbient` under the
abelianized `qE`. Both sides are elements of `Abelianization G`. The
equation has the source orientation: the transported value is on the left.

The proposition is a small general fact about abelianizations of arbitrary
groups in `Type`. Nothing in it refers to fields, Galois groups or norm
residues. In the source it is used once, in the proof at line 380 of the
later file `AmbientPrimeSymbolSetup.lean`.

## Reused declarations

The statement uses only Mathlib: `Abelianization`, `Abelianization.of`,
`MulEquiv.abelianizationCongr`, `MulEquiv.symm`, `Additive`,
`Additive.ofMul` and `Additive.toMul`. The sole import is
`Mathlib.GroupTheory.Abelianization.Defs`. It defines the abelianization and
`MulEquiv.abelianizationCongr`, and its own imports supply the `Additive`
type tags.

## Library search

The whole Library at commit `8cfcc2bff12a9cb7a1f89a973a0c59f2dc39865a`
(whose Lean files are identical to those of the current base
`125eb56832ba1e00c87d0a67981fe249453d68b4`) was
searched for `abelianizationCongr`. Mathlib's `MulEquiv.abelianizationCongr`
occurs only in the NYLL statement
`Langlands.NYLL.PortInternal.M260.d006Statement`
(`.../IntermediateFieldNormResidueNaturality/U006/Statements.lean`). That
statement is about `Abelianization.equivOfComm` for an isomorphism onto a
commutative group, which is a different assertion. The host
`Langlands.LocalClassField.abelianizationCongr` in
`Langlands/LocalClassField/AbelianizationTransport.lean` and its uses are
about continuous isomorphisms and the topological abelianization, a
different construction. No Library declaration states this transport
equation, so nothing in the Library already covers M284.001. The Mathlib
simp lemmas `MulEquiv.abelianizationCongr_of` and
`MulEquiv.abelianizationCongr_symm` are building blocks for a proof, not
this statement.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeWitness.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeWitness.lean>).
The complete file was read; its SHA-256 is
`e994e84e592e80c1452852d6b3ef89a36527c36b2ec64a84775628ff3695894d`.
The header is at lines 1–5, the imports at 7–9, the module docstring at
11–17, `noncomputable section` at 21, the namespace at 23 and the `open`
lines at 25–27.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M284.001, `LocalClassFieldTheory.abelianizationCongr_symm_eq_primeTarget` | docstring 29–30, signature 31–47, proof 48–66 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.abelianizationCongr_symm_eq_primeTargetStatement` |

The source signature is

```lean
theorem abelianizationCongr_symm_eq_primeTarget
    {Q₀ G₀ G : Type}
    [Group Q₀] [Group G₀] [Group G]
    (q₀ : Q₀ ≃* G₀)
    (qE : Q₀ ≃* G)
    (qAmbient : Q₀)
    (r : Additive (Abelianization G₀))
    (hprime :
      r =
        Additive.ofMul
          (q₀.abelianizationCongr
            (Abelianization.of qAmbient))) :
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul r)) =
      qE.abelianizationCongr
        (Abelianization.of qAmbient)
```

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the asserted type directly from the pinned original on
13 November 2026 and made these changes:

- The theorem becomes a Prop-valued definition with the `Statement` suffix.
  All ten binders move inside the proposition in the same order, with the
  same binder kinds and the source's universe-zero `Type`. The proof is
  omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
- The named hypothesis `hprime` becomes an anonymous premise of the same
  type.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and the NYLL
  `AmbientNormResidue` and `AmbientPrimeNormTransport` modules) are replaced
  by the single Mathlib module `Mathlib.GroupTheory.Abelianization.Defs`.
  The statement uses nothing from the NYLL modules.
- The `noncomputable section`, the `open` lines and all other declarations
  of the source file are omitted. The statement needs none of the opened
  namespaces.

The original docstring is kept on the definition. No instance or simp
attribute is installed. No shared draft or other worker's unpublished work
was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this statement. Its truth proof belongs to a
separate proof unit published after this statement is accepted. The source
definitions `ambientEmbeddedPrimeWitness` (M284.002, line 68 onward) and
the later M284 rows are separate units.
