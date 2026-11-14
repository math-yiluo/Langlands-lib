# Abelianized restriction between concrete relative Galois groups: definition

This module defines one declaration,
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldAbelianizedRestriction`.
It adapts source row M277.005, the definition
`LocalClassFieldTheory.abstractFixedFieldAbelianizedRestriction`, keeping
the source section variables, docstring, binders and body unchanged. The
definition installs no instance and proves no theorem.

## Telescope

The source declares the section variables

```lean
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
```

and the adapted module repeats this line. Lean includes in a definition
only the section variables that it uses, together with instance arguments
that it uses. Inspection of the compiled declaration (`#check`, Lean
v4.34.0) gives the telescope

```lean
abstractFixedFieldAbelianizedRestriction :
  (k Ω : Type) → [Field k] → [Field Ω] → [Algebra k Ω] → [IsGalois k Ω] →
  (K K' L L' : ClosedSubgroup Gal(Ω/k)) →
  (hLK : ↑L ≤ ↑K) → (hL'K' : ↑L' ≤ ↑K') → ↑K' ≤ ↑K → ↑L' ≤ ↑L →
  [hLnormal : (extensionSubgroup K L hLK).Normal] →
  [hL'normal : (extensionSubgroup K' L' hL'K').Normal] →
  Additive (Abelianization
      Gal(abstractRelativeFixedField k Ω hL'K' / abstractFixedField k Ω K')) →+
    Additive (Abelianization
      Gal(abstractRelativeFixedField k Ω hLK / abstractFixedField k Ω K))
```

Here `↑L ≤ ↑K` is `L.toSubgroup ≤ K.toSubgroup`, and so on. The inclusions
`hK'K` and `hL'L` are named in the source signature; `#check` prints them
without names because the result type does not depend on them. Unlike the
neighbouring M277.004, this definition does use `[IsGalois k Ω]`: the
published equivalence `abstractExtensionQuotientEquivGaloisGroup` takes it
as an instance argument. So it is a parameter, as in the source (Lean
v4.35.0-rc2, whose rule for including section variables is the same).

| Parameter | Kind and meaning |
| --- | --- |
| `k Ω : Type` | Explicit field types, in universe zero as in the source |
| `[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]` | `Ω` is a Galois extension of `k`, possibly infinite |
| `K K' L L' : ClosedSubgroup Gal(Ω/k)` | Explicit closed subgroups of the Galois group |
| `hLK`, `hL'K'`, `hK'K`, `hL'L` | Explicit inclusions `L ≤ K`, `L' ≤ K'`, `K' ≤ K`, `L' ≤ L` |
| `[hLnormal]`, `[hL'normal]` | Instance hypotheses that `L` is normal in `K` and `L'` is normal in `K'`, as subgroups of `K` and `K'` |

## Meaning

Write `Ω^H` for `abstractFixedField k Ω H`, the fixed field of a closed
subgroup `H`. The four inclusions give the square of fields
`Ω^K ⊆ Ω^{K'} ⊆ Ω^{L'}` and `Ω^K ⊆ Ω^L ⊆ Ω^{L'}`.
`abstractRelativeFixedField k Ω hLK` is `Ω^L` viewed as an intermediate
field over `Ω^K`, and similarly for `hL'K'`. The source type is thus the
abelianized Galois group of `Ω^{L'} / Ω^{K'}` and the target type that of
`Ω^L / Ω^K`, both written additively.

The body is

```lean
MonoidHom.toAdditive
  ((abstractExtensionQuotientEquivGaloisGroup
    k Ω K L hLK hLnormal).abelianizationCongr.toMonoidHom.comp
    ((normResidueNaturalityAbelianizedRestriction K K' L L'
      hLK hL'K' hK'K hL'L).comp
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K' L' hL'K'
        hL'normal).abelianizationCongr.symm.toMonoidHom))
```

It composes three multiplicative homomorphisms:

1. The inverse of the abelianization of
   `abstractExtensionQuotientEquivGaloisGroup k Ω K' L' hL'K' hL'normal`,
   the published group isomorphism
   `K' ⧸ (L' as a subgroup of K') ≃* Gal(Ω^{L'} / Ω^{K'})`.
   `MulEquiv.abelianizationCongr` is Mathlib's induced isomorphism of
   abelianizations.
2. `normResidueNaturalityAbelianizedRestriction K K' L L' …`, the
   class-formation map
   `Abelianization (K' ⧸ L') →* Abelianization (K ⧸ L)`, which is
   `Abelianization.map` of the map of quotients induced by the inclusion
   `K' ≤ K` (well defined because `L' ≤ L`).
3. The abelianization of the corresponding isomorphism
   `K ⧸ (L as a subgroup of K) ≃* Gal(Ω^L / Ω^K)`.

`MonoidHom.toAdditive` writes the composite additively. So the definition
is the class-formation abelianized restriction, transported to the actual
relative Galois groups through the two canonical quotient/Galois
isomorphisms. The source's next theorem,
`abstractFixedFieldAbelianizedRestriction_on_representative`, shows that it
is restriction of automorphisms from `Ω^{L'}` to `Ω^L`; that theorem is a
separate unit and is not claimed here.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M086.019, `ClassFormation.normResidueNaturalityAbelianizedRestriction` | `Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U019.Definitions` |
| M099.017, `LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup` | `Langlands.NYLL.LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Equivalences.Definitions` |
| `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (an abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`), reached through the first import |
| M099.001 and M099.009, `abstractFixedField` and `abstractRelativeFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` and `.abstractRelativeFixedField`, reached through the second import |
| Mathlib `ClosedSubgroup`, `IsGalois`, `Abelianization`, `MulEquiv.abelianizationCongr`, `Additive`, `MonoidHom.toAdditive` | Used unchanged |

The module imports exactly the two published modules named in the first
two rows.

## Library search

The whole Library at commit `58ad0f796899b4aa457077d0146815c24758f739` was
searched for `abstractFixedFieldAbelianizedRestriction` (no occurrence),
for every use of `normResidueNaturalityAbelianizedRestriction`, of
`abstractExtensionQuotientEquivGaloisGroup` and of `abelianizationCongr`.
`normResidueNaturalityAbelianizedRestriction` is used only in its own
modules (`Reciprocity/Main/U019`, `U020`) and in the M288.001 statement and
proof (`FixedFieldIntrinsicReciprocity/NormRestriction/U001`), which
transport it through the `quotientEquiv` isomorphisms of ambient embedded
presentations inside a statement, and define no map.
`abstractExtensionQuotientEquivGaloisGroup` is used only in its own module
and in a statement about its values
(`AbstractFixedFieldUnits/Action/Statements`). The other NYLL uses of
`abelianizationCongr` (`AmbientPrimeWitness/U001`,
`IntermediateFieldNormResidueNaturality/U006`) are statements about other
equivalences. Outside `Langlands/NYLL`, the Library has restriction maps of
abelianized Galois groups of finite extensions (for example
`Abelianization.map (AlgEquiv.restrictNormalHom E)` in
`Langlands/ClassFieldTheory/Local/FiniteAbelianizedArtin.lean`) and
abelianizations of continuous isomorphisms
(`Langlands/LocalClassField/AbelianizationTransport.lean`), but none of
them is stated for `abstractFixedField` or is the transported
class-formation map that the later source declarations name. So nothing in
the Library already covers M277.005.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean>).
The file was read; its SHA-256 is
`f05e7d0475ae6837a3a41da9e3185201178a01a78da0afc37557b9314bc42981`.
The header is at lines 1–5, the imports at 7–11, the module docstring at
13–19, `noncomputable section` at 23, the namespace at 25, the `open` lines
at 27–28 and the `variable` line at 30.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M277.005, `LocalClassFieldTheory.abstractFixedFieldAbelianizedRestriction` | docstring 107–109, signature 110–123, body 124–131 | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldAbelianizedRestriction` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 56 extracted the definition directly from the pinned original on
14 November 2026 and made these changes:

- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix.
  The name, docstring, `variable` line, signature and body are unchanged.
- The source imports (the NYLL modules `FixedFieldRelativeNorm`,
  `LocalClassFieldAxiom`, `LocalHenselianValuation` and
  `AbstractClassFieldTheory.Reciprocity.Main`, and
  `Mathlib.FieldTheory.Galois.Notation`) are replaced by the two published
  modules listed above.
- The source `open` lines are replaced by
  `open Langlands.NYLL.CyclicCohomology Langlands.NYLL.ClassFormation`, the
  only opened namespaces whose names the definition uses
  (`extensionSubgroup` and `normResidueNaturalityAbelianizedRestriction`).
- All other declarations of the source file are omitted.

No instance or simp attribute is installed. No shared draft or other
worker's unpublished work was reused.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0
notice, followed by a dated modification record. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Scope

This unit contains only this definition. The other declarations of the
source file, including `abstractFixedFieldUnitsInclusion` (M277.001),
`abstractFixedFieldNormResidueSymbol` (M277.003),
`abstractFixedFieldNormUnits` (M277.004) and
`abstractFixedFieldAbelianizedRestriction_on_representative`, are separate
units.
