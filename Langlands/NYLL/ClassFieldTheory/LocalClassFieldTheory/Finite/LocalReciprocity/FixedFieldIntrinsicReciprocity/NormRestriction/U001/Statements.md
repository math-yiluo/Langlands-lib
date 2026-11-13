# Restriction of embedded Galois actions on ambient quotient representatives: statement

This module defines one closed proposition:

- `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestrictionStatement : Prop`,
  the statement phase of source row M288.001, the theorem
  `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestriction`.

The module contains no proof. A separate proof child will prove it under the
name
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestriction`.

## Complete closed telescope

The definition has no parameters or universe variables. Its body is

```lean
∀ (K K' L L' : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K']
  [Field L] [Field L']
  [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L']
  [IsScalarTower K K' L'] [IsScalarTower K L L']
  [FiniteDimensional K K'] [Algebra.IsSeparable K K']
  [Valuation.HasExtension
    (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [FiniteDimensional K' L'] [IsAbelianGalois K' L']
  {jLower : L →ₐ[K] SeparableClosure K}
  {jUpper : L' →ₐ[K] SeparableClosure K}
  (lower : AmbientEmbeddedFixedFieldPresentation K K L jLower)
  (upper : AmbientEmbeddedFixedFieldPresentation K K' L' jUpper)
  (hH'H : upper.base.field.toSubgroup ≤ lower.base.field.toSubgroup)
  (hJ'J : upper.extension.field.toSubgroup ≤
    lower.extension.field.toSubgroup)
  [(extensionSubgroup lower.base.field lower.extension.field
      lower.extension.below).Normal]
  [Finite
    (lower.base.field.toSubgroup ⧸
      extensionSubgroup lower.base.field lower.extension.field
        lower.extension.below)]
  [(extensionSubgroup upper.base.field upper.extension.field
      upper.extension.below).Normal]
  [Finite
    (upper.base.field.toSubgroup ⧸
      extensionSubgroup upper.base.field upper.extension.field
        upper.extension.below)]
  [Finite
    ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
      extensionSubgroup
        (baseField Gal(SeparableClosure K/K))
        lower.base.field (le_baseField lower.base.field))]
  [Finite
    ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
      extensionSubgroup
        (baseField Gal(SeparableClosure K/K))
        upper.base.field (le_baseField upper.base.field))]
  [Finite
    (lower.base.field.toSubgroup ⧸
      extensionSubgroup lower.base.field upper.base.field hH'H)]
  (restrictActual : Gal(L'/K') →* Gal(L/K)),
  (∀ x : L, jUpper (algebraMap L L' x) = jLower x) →
    (∀ (τ : Gal(L' / K')) (x : L),
      jLower (restrictActual τ x) =
        jUpper (τ (algebraMap L L' x))) →
      ∀ (z : Abelianization
        (upper.base.field.toSubgroup ⧸
          extensionSubgroup upper.base.field upper.extension.field
            upper.extension.below)),
        restrictActual
            ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
              ((upper.extension.extensionQuotientMulEquiv.symm.trans
                upper.quotientEquiv).abelianizationCongr z)) =
          (Abelianization.equivOfComm (H := Gal(L / K))).symm
            ((lower.extension.extensionQuotientMulEquiv.symm.trans
              lower.quotientEquiv).abelianizationCongr
              (normResidueNaturalityAbelianizedRestriction
                lower.base.field upper.base.field
                lower.extension.field upper.extension.field
                lower.extension.below upper.extension.below
                hH'H hJ'J z))
```

It has the forty-five binders of the source theorem, in the source order:

| Binder | Kind and meaning |
| --- | --- |
| `K K' L L' : Type` | Explicit types, in universe zero as in the source |
| `[Field K]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]` | Instance-implicit structures making `K` a nonarchimedean local field |
| `[Field K']`, `[ValuativeRel K']`, `[TopologicalSpace K']`, `[IsNonarchimedeanLocalField K']` | The same four structures on `K'` |
| `[Field L]`, `[Field L']` | Instance-implicit field structures |
| `[Algebra K K']`, `[Algebra K L]`, `[Algebra K L']`, `[Algebra K' L']`, `[Algebra L L']` | Instance-implicit algebra structures of the square `K ⊆ K' ⊆ L'`, `K ⊆ L ⊆ L'` |
| `[IsScalarTower K K' L']`, `[IsScalarTower K L L']` | Instance-implicit: both towers to `L'` are compatible |
| `[FiniteDimensional K K']`, `[Algebra.IsSeparable K K']` | Instance-implicit: `K'` is finite and separable over `K` |
| `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation K')]` | Instance-implicit: the valuation of `K'` extends that of `K` |
| `[FiniteDimensional K L]`, `[IsAbelianGalois K L]` | Instance-implicit: `L/K` is finite abelian Galois |
| `[FiniteDimensional K' L']`, `[IsAbelianGalois K' L']` | Instance-implicit: `L'/K'` is finite abelian Galois |
| `{jLower : L →ₐ[K] SeparableClosure K}` | Implicit `K`-embedding of `L` into Mathlib's separable closure of `K` |
| `{jUpper : L' →ₐ[K] SeparableClosure K}` | Implicit `K`-embedding of `L'` into the same separable closure |
| `(lower : AmbientEmbeddedFixedFieldPresentation K K L jLower)` | Explicit ambient fixed-field presentation of `L/K` along `jLower` |
| `(upper : AmbientEmbeddedFixedFieldPresentation K K' L' jUpper)` | Explicit ambient fixed-field presentation of `L'/K'` along `jUpper` |
| `(hH'H : …)` | Explicit: the ambient base subgroup of `upper` lies in that of `lower` (`K'` lies over `K`) |
| `(hJ'J : …)` | Explicit: the ambient top subgroup of `upper` lies in that of `lower` (`L'` lies over `L`) |
| `[… .Normal]` (source `hJnormal`) | Instance-implicit: the top subgroup of `lower` is normal in its base subgroup |
| `[Finite …]` (source `_hJfinite`) | Instance-implicit: the ambient quotient of `lower` is finite |
| `[… .Normal]` (source `hJ'normal`) | Instance-implicit: the top subgroup of `upper` is normal in its base subgroup |
| `[Finite …]` (source `_hJ'finite`) | Instance-implicit: the ambient quotient of `upper` is finite |
| `[Finite …]` (source `_hHabsolute`) | Instance-implicit: the base subgroup of `lower` has finite index in the full Galois group |
| `[Finite …]` (source `_hH'absolute`) | Instance-implicit: the base subgroup of `upper` has finite index in the full Galois group |
| `[Finite …]` (source `_hH'finite`) | Instance-implicit: the base subgroup of `upper` has finite index in that of `lower` |
| `(restrictActual : Gal(L'/K') →* Gal(L/K))` | Explicit group homomorphism between the actual Galois groups |
| premise (source `hbase`) | The embeddings are compatible: `jUpper (algebraMap L L' x) = jLower x` for all `x : L` |
| premise (source `hcompat`) | `restrictActual` is restriction through the embeddings: `jLower (restrictActual τ x) = jUpper (τ (algebraMap L L' x))` |
| `(z : Abelianization …)` | Explicit element of the abelianized ambient quotient of `upper` |

Every binder is quantified inside the proposition. The source names the seven
instance-implicit hypotheses `hJnormal`, `_hJfinite`, `hJ'normal`,
`_hJ'finite`, `_hHabsolute`, `_hH'absolute` and `_hH'finite`; nothing in the
type refers to these names, so they are anonymous instance binders here, in the
same positions and still instance-implicit. The source also names the explicit
hypotheses `hbase` and `hcompat`; the conclusion mentions neither, so they
appear as unnamed implication premises in exactly their source positions. An
implication premise is an explicit, unnamed binder, so no binder kind changes.

## Meaning

For a closed subgroup `H` of the absolute Galois group
`Gal(SeparableClosure K/K)`, the published framework reads `H` as an abstract
field (its fixed field). The structure
`Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation K F E j`
(source row M282.002) records, for a finite Galois extension `E/F` embedded in
`SeparableClosure K` by `j`, an ambient base subgroup `base.field` fixing the
image of `F`, a finite Galois subextension `extension` whose subgroup
`extension.field` fixes the image of `E`, and a group isomorphism
`quotientEquiv : extension.extensionQuotient ≃* Gal(E/F)` from the ambient
quotient `base.field / extension.field` to the actual Galois group, acting
through `j`. Here `lower` presents `L/K` and `upper` presents `L'/K'`.

`extension.extensionQuotientMulEquiv.symm.trans quotientEquiv` identifies the
ambient quotient `base.field.toSubgroup ⧸ extensionSubgroup …` with the actual
Galois group, `MulEquiv.abelianizationCongr` (Mathlib) applies this
identification to abelianizations, and `(Abelianization.equivOfComm).symm`
(Mathlib) returns from the abelianization of the commutative Galois group to
the group itself. The scoped instances opened by `open scoped
IsMulCommutative` turn the `IsMulCommutative` part of `IsAbelianGalois` into
the `CommGroup` structure that `Abelianization.equivOfComm` needs, as in the
source.

`Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction`
(source row M086.019) is the map
`Abelianization (H' ⧸ J') →* Abelianization (H ⧸ J)` induced by the inclusion
`H' ≤ H` of ambient subgroups with `J' ≤ J`.

The proposition says: if the embeddings are compatible (`hbase`) and
`restrictActual` is the restriction `Gal(L'/K') → Gal(L/K)` read through
`jLower` and `jUpper` (`hcompat`), then for every `z` in the abelianized ambient
quotient of `upper`, sending `z` to `Gal(L'/K')` and restricting gives the same
element of `Gal(L/K)` as first applying the ambient abelianized restriction and
then sending the result to `Gal(L/K)`. In other words the two presentations
intertwine the actual restriction with the ambient restriction of quotients.

The base-field presentation `lower` uses `K` as its own base field. Its
structure parameters `[Algebra K K]`, `[IsScalarTower K K L]`,
`[FiniteDimensional K K]`, `[Algebra.IsSeparable K K]` and
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation K)]`
are not binders: instance search finds them from Mathlib, exactly as in the
source. The instance arguments of `extensionSubgroup` and
`normResidueNaturalityAbelianizedRestriction` that ask for normality are filled
by the anonymous normality binders.

## Reused declarations

| Source unit and original declaration | Declaration used |
| --- | --- |
| M282.002, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation` | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation`, module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientNormResidue.U002.Definitions` (imported) |
| M086.019, `ClassFormation.normResidueNaturalityAbelianizedRestriction` | `Langlands.NYLL.ClassFormation.normResidueNaturalityAbelianizedRestriction`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U019.Definitions` (imported; see the prerequisite note below) |
| M010.005, `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField`, module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` (imported) |
| `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField` (published; through the imports) |
| `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (published; through the imports) |
| `ClassFormation.FiniteGaloisSubextension` and its `field`, `below`, `extensionQuotientMulEquiv` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` (published; through the imports) |
| Mathlib `Abelianization`, `Abelianization.equivOfComm`, `MulEquiv.abelianizationCongr` | Module `Mathlib.GroupTheory.Abelianization.Defs` (imported explicitly, as in the source) |
| Mathlib `IsAbelianGalois` | Module `Mathlib.FieldTheory.Galois.Abelian` (imported explicitly) |
| Mathlib `IsNonarchimedeanLocalField`, `ValuativeRel.valuation`, `Valuation.HasExtension`, `SeparableClosure`, `Algebra.IsSeparable`, `FiniteDimensional`, `IsScalarTower`, `AlgHom`, `MonoidHom` | Used unchanged, through the imports' Mathlib closure |

The type mentions the proof term `le_baseField lower.base.field` (as the
containment argument of `extensionSubgroup`), so the published proof module
of M010.005 is imported. The adaptation opens `Langlands.NYLL.CyclicCohomology`
and `Langlands.NYLL.ClassFormation`, the published namespaces corresponding to
the source's `open CyclicCohomology` and `open ClassFormation`, so these names
resolve without qualification.

Prerequisite note: the M086.019 module is the candidate
`3a839135-8a44-4c51-9463-5e4826bee89b`, accepted and awaiting integration
when this statement was prepared. Its files are identical in this workspace.

## Library search

The whole Library at commit `6948120d6f1b811bab3b7ee04997f6fba7aa9908` was
searched for `quotientRestriction`, for every use of
`AmbientEmbeddedFixedFieldPresentation` and of
`normResidueNaturalityAbelianizedRestriction`, and for uses of
`abelianizationCongr` and `Abelianization.equivOfComm`. Unrelated
`quotientRestriction` declarations occur in
`Langlands/GroupScheme/Torus/QuotientCharacters.lean`,
`Tate/ZeroTransferDefinitions` and `Global/CocompactFieldRestriction`.
The presentation is used
only in its own defining module. The `abelianizationCongr` uses in
`Langlands/ClassFieldTheory/Local/` transport Weil-group abelianizations along
fixed equivalences and say nothing about ambient fixed-field quotients. So
nothing in the Library already covers M288.001.

## Original source

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/NormRestriction.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/NormRestriction.lean>).
The complete file was read; its SHA-256 is
`cd6f508f2695bb024ae28041740f78edbd1cb03492d287248ddaba7bb115e9a3`.
The header is at lines 1–5, the imports at 7–8, the module docstring at
10–14, `noncomputable section` at 18, the namespace at 20 and the `open`
lines at 22–24.

| Source unit and original declaration | Source lines | Adapted declaration |
| --- | --- | --- |
| M288.001, `LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestriction` | docstring 26–27, signature 28–98, proof 99–186 (omitted) | `Langlands.NYLL.LocalClassFieldTheory.AmbientEmbeddedFixedFieldPresentation.quotientRestrictionStatement` |

The source signature (lines 28–98) is reproduced in the telescope above
with these differences only: the theorem's binders are quantified inside the
proposition, the seven instance hypotheses lose their names, and `hbase` and
`hcompat` lose their names. The source writes the instance hypotheses as
`[hJnormal : …]`, `[_hJfinite : Finite …]`, `[hJ'normal : …]`,
`[_hJ'finite : Finite …]`, `[_hHabsolute : Finite …]`,
`[_hH'absolute : Finite …]` and `[_hH'finite : Finite …]`, and the two
premises as

```lean
    (hbase : ∀ x : L,
      jUpper (algebraMap L L' x) = jLower x)
    (hcompat : ∀ (τ : Gal(L' / K')) (x : L),
      jLower (restrictActual τ x) =
        jUpper (τ (algebraMap L L' x)))
```

The source proof (omitted here) reduces `z` to the class of a representative
`sigma`, rewrites with `normResidueNaturalityAbelianizedRestriction_of_mk`
(source row M086.020) and Mathlib's `MulEquiv.abelianizationCongr_of`, and then
compares the two Galois actions pointwise through `jLower`, using `hcompat`,
`quotientEquiv_mk_apply` of both presentations and `hbase`. The proof phase
therefore needs the published proof of M086.020. The next declaration of the
file,
`AmbientEmbeddedFixedFieldPresentation.fixedFieldNormResidueTransport`
(M288.002), starts with its docstring at line 188.

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
  All forty-five binders move inside the proposition in the same order, with
  the same binder kinds and the source's universe-zero `Type`. The proof is
  omitted for the separate proof phase.
- The seven named instance hypotheses become anonymous instance binders, and
  the unreferenced hypotheses `hbase` and `hcompat` become unnamed
  implication premises, all in their source positions.
- The namespace `LocalClassFieldTheory` gets the `Langlands.NYLL` prefix. Of
  the source's `open` lines, only the published counterparts of
  `CyclicCohomology` and `ClassFormation` and the scoped `IsMulCommutative`
  opening are kept; `LocalFieldTheory`, `RamificationTheory`, `KummerTheory`
  and the scoped `ValuativeRel` opening are not needed by the type.
- The NYLL source import (`AmbientPrimeComparison`) is replaced by the
  published modules defining the ambient presentation (M282.002), the
  abelianized restriction (M086.019) and `le_baseField` (M010.005), together
  with Mathlib's `Mathlib.FieldTheory.Galois.Abelian` for `IsAbelianGalois`.
  The source's Mathlib import `Mathlib.GroupTheory.Abelianization.Defs` is
  kept.
- The `noncomputable section` and all other declarations of the source file
  are omitted. A proposition definition needs no noncomputable section.

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

This unit contains only this statement. Its truth proof belongs to a separate
proof unit published after the statement is accepted. The later declarations
of the source file (M288.002–M288.004, from line 188 onward, ending with
`abelianLocalArtinMonoidHom_norm_restriction` at line 686) are separate units.
