# Unit norms and norm classes under compatible field equivalences: statements

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phases of source rows
M283.006 and M283.007:

- `normUnits_mapEquivStatement`, for the source theorem `normUnits_mapEquiv`;
- `normClass_mapEquivStatement`, for the source theorem `normClass_mapEquiv`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither has a proof here. Later proof children will prove them
under the names `Langlands.NYLL.LocalClassFieldTheory.normUnits_mapEquiv` and
`Langlands.NYLL.LocalClassFieldTheory.normClass_mapEquiv`.

## Common parameters

Both propositions universally quantify, in the source order,

```lean
(F E F₀ E₀ : Type)
  [Field F] [Field E] [Field F₀] [Field E₀]
  [Algebra F E] [Algebra F₀ E₀]
  (phiF : F ≃+* F₀) (phiE : E ≃+* E₀)
  (_hcomm :
    RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
      RingHom.comp phiE.toRingHom (algebraMap F E))
```

All four fields are in `Type` (universe zero), as in the source. `F ⊆ E` and
`F₀ ⊆ E₀` are arbitrary field extensions given by the supplied algebra
structures. There is no finite-dimensionality, separability, Galois,
valuation or topology hypothesis. `phiF` and `phiE` are ring equivalences,
and `_hcomm` says that they commute with the two algebra maps:
`algebraMap F₀ E₀ (phiF x) = phiE (algebraMap F E x)` for all `x : F`, stated
as an equality of ring homomorphisms `F →+* E₀`.

## The two propositions

`normUnits_mapEquivStatement` continues with `(y : Eˣ)` and concludes

```lean
Langlands.NYLL.LocalFieldTheory.normUnits F₀ E₀
    (Units.mapEquiv phiE.toMulEquiv y) =
  Units.mapEquiv phiF.toMulEquiv
    (Langlands.NYLL.LocalFieldTheory.normUnits F E y)
```

So the unit norm from `E₀` to `F₀` of the transported unit `phiE y` is the
transport by `phiF` of the unit norm of `y` from `E` to `F`. Here
`Langlands.NYLL.LocalFieldTheory.normUnits K L : Lˣ →* Kˣ` is the published
`Units.map (Algebra.norm K)`. With no finite-dimensionality hypothesis,
Mathlib's `Algebra.norm` is `1` on infinite extensions, so the statement also
covers that case.

`normClass_mapEquivStatement` continues with `(a x : Fˣ)` and a hypothesis
`(_h : normClass F E a = normClass F E x)`, and concludes

```lean
Langlands.NYLL.LocalFieldTheory.normClass F₀ E₀
    (Units.mapEquiv phiF.toMulEquiv a) =
  Langlands.NYLL.LocalFieldTheory.normClass F₀ E₀
    (Units.mapEquiv phiF.toMulEquiv x)
```

So if two units of `F` have the same class modulo the norms from `E`, then
their images under `phiF` have the same class modulo the norms from `E₀`.
Here `Langlands.NYLL.LocalFieldTheory.normClass K L : Kˣ →* NormQuotient K L`
is the published quotient map onto `Kˣ ⧸ localNormSubgroup K L`, where
`localNormSubgroup K L` is the range of `normUnits K L`.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M092.002, `LocalFieldTheory.normUnits` | `Langlands.NYLL.LocalFieldTheory.normUnits` (module `Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`) |
| M093.005, `LocalFieldTheory.normClass` | `Langlands.NYLL.LocalFieldTheory.normClass` (module `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U005.Definitions`) |

The source proof of M283.007 also uses M093.031
`normClass_eq_iff_exists_norm_div`. It is published as
`Langlands.NYLL.LocalFieldTheory.normClass_eq_iff_exists_norm_div`. The
statements do not need it, so this module does not import it.

The Library has a similar theorem for a different norm map:
`Langlands.LocalClassField.FiniteArtinTransport.normUnits_map` in
`Langlands/ClassFieldTheory/Local/FiniteArtinTransport.lean`. It is stated for
`Langlands.LocalClassField.normUnits`, which is a separate constant that
requires `[FiniteDimensional K E]` and `[FiniteDimensional K' E']`, and it
allows the four fields to lie in four arbitrary universes. M283.006 is
stated for the NYLL constant `Langlands.NYLL.LocalFieldTheory.normUnits`
without any finite-dimensionality hypothesis. So the Library theorem does
not cover it. A search of the Library found no public theorem about
`Langlands.NYLL.LocalFieldTheory.normUnits` or `normClass` under field
equivalences.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean>).
The complete file was read and its SHA-256 verified as
`b430f3810416cb42cc7c61df63be3691b219a5fe39c0bc7c0c2a74292298bfa0`.
The header occupies lines 1–5, the module docstring lines 10–16, the
`noncomputable section` line 20, the namespace line 22 and the `open`
lines 24–26.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M283.006, `LocalClassFieldTheory.normUnits_mapEquiv` | docstring 187–188, signature 189–199, proof 200–209 | `Langlands.NYLL.LocalClassFieldTheory.normUnits_mapEquivStatement` |
| M283.007, `LocalClassFieldTheory.normClass_mapEquiv` | docstring 211, signature 212–224, proof 225–231 | `Langlands.NYLL.LocalClassFieldTheory.normClass_mapEquivStatement` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and its proof is omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source refers to `normUnits` and `normClass` through
  `open LocalFieldTheory`. The adaptation writes the full published names
  `Langlands.NYLL.LocalFieldTheory.normUnits` and
  `Langlands.NYLL.LocalFieldTheory.normClass` and has no `open` lines.
- The hypotheses `hcomm` and `h` are renamed `_hcomm` and `_h`. The
  propositions do not refer to them, and Lean's unused-variable linter warns
  about named unused binders in a `∀`. The types are unchanged.
- The source imports (`Mathlib.FieldTheory.Galois.Basic` and
  `Nyll...FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport`) are
  replaced by the two published modules that define `normUnits` and
  `normClass`.
- The `noncomputable section` is omitted. All other declarations of the
  source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only these two statement targets. Their proofs belong
to separate proof units.
