# NYLL M040: finite Galois subextension targets

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
(file SHA-256 `c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

All adapted names use the prefix
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.`, and all original
names the prefix `ClassFormation.FiniteGaloisSubextension.`. The source lines
are those of the theorem's binders and statement; the proof is omitted.

| Unit | Original theorem | Source lines | Adapted Prop-valued target |
| --- | --- | --- | --- |
| M040.012 | `extensionQuotientMk_apply` | 111–115 | `extensionQuotientMk_applyStatement` |
| M040.013 | `extensionQuotientMk_eq_one_iff` | 120–123 | `extensionQuotientMk_eq_one_iffStatement` |
| M040.014 | `extensionQuotientMk_surjective` | 140–141 | `extensionQuotientMk_surjectiveStatement` |
| M040.018 | `toGaloisSubextension_isTotallyRamified_iff` | 176–178 | `toGaloisSubextension_isTotallyRamified_iffStatement` |
| M040.020 | `isTotallyRamified_toGaloisSubextension` | 191–194 | `isTotallyRamified_toGaloisSubextensionStatement` |
| M040.022 | `isTotallyRamified_iff_image_le` | 205–209 | `isTotallyRamified_iff_image_leStatement` |
| M040.024 | `finite_extension_trans` | 225–233 | `finite_extension_transStatement` |
| M040.025 | `finite_extension_over_intermediate` | 248–255 | `finite_extension_over_intermediateStatement` |
| M040.030 | `compositum_le_left` | 401–402 | `compositum_le_leftStatement` |
| M040.031 | `compositum_le_right` | 406–407 | `compositum_le_rightStatement` |

## Telescopes and statements

Every target has the source section binders implicit `{G : Type u}`,
`[Group G]`, `[TopologicalSpace G]` (source line 31). Each target then takes
exactly the source theorem's remaining binders in source order and returns,
as its `Prop` body, exactly the source statement:

- M040.012: `{K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
  (k : K.toSubgroup)`;
  `L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
  (QuotientGroup.mk k : K.toSubgroup ⧸ extensionSubgroup K L.field L.below)`.
- M040.013: the same binders;
  `L.extensionQuotientMk k = 1 ↔ k ∈ extensionSubgroup K L.field L.below`.
- M040.014: `{K} (L)`; `Function.Surjective L.extensionQuotientMk`.
- M040.018: `{K} (L) (D : DegreeData G)`;
  `L.toGaloisSubextension.IsTotallyRamified D ↔ L.IsTotallyRamified D`.
- M040.020: `{K} (L) (D : DegreeData G) (hL : L.IsTotallyRamified D)`;
  `L.toGaloisSubextension.IsTotallyRamified D`. The hypothesis `hL` is kept
  as a binder although the conclusion does not mention it.
- M040.022: `{K} (L) (D : DegreeData G)`; `L.IsTotallyRamified D ↔
  K.toSubgroup.map D.degree.toMonoidHom ≤
  L.field.toSubgroup.map D.degree.toMonoidHom`.
- M040.024: `{P L K : ClosedSubgroup G}`,
  `(hPL : P.toSubgroup ≤ L.toSubgroup)`, `(hLK : L.toSubgroup ≤ K.toSubgroup)`,
  `[hPLfinite : Finite (L.toSubgroup ⧸ extensionSubgroup L P hPL)]`,
  `[hLKfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]`;
  `Finite (K.toSubgroup ⧸ extensionSubgroup K P (hPL.trans hLK))`.
- M040.025: `{P M K : ClosedSubgroup G}`,
  `(hPK : P.toSubgroup ≤ K.toSubgroup)`, `(hMK : M.toSubgroup ≤ K.toSubgroup)`,
  `(hPM : P.toSubgroup ≤ M.toSubgroup)`,
  `[hPKfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K P hPK)]`;
  `Finite (M.toSubgroup ⧸ extensionSubgroup M P hPM)`. The hypothesis `hMK`
  is kept although the conclusion does not mention it.
- M040.030: `{K} (L₁ L₂ : FiniteGaloisSubextension K)`;
  `(L₁.compositum L₂).field.toSubgroup ≤ L₁.field.toSubgroup`.
- M040.031: the same binders;
  `(L₁.compositum L₂).field.toSubgroup ≤ L₂.field.toSubgroup`.

Here `{K}` is the source namespace variable `{K : ClosedSubgroup G}` (line 46)
and `(L)` is `(L : FiniteGaloisSubextension K)`. In M040.024 and M040.025 the
source theorems bind their own `{P L K}` or `{P M K}`, so the namespace variable
`K` is not part of their telescopes; Lean likewise omits it from the targets.
A `#check` of each target confirmed these telescopes, including the source
names `hPLfinite`, `hLKfinite` and `hPKfinite` of the instance binders.

## Reused declarations

The data come from the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`
(port of M040.001–011, 015, 028, 029). Also used are the published
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), with its
source spelling, `Langlands.NYLL.ClassFormation.DegreeData` (M010.002) and
its `degree` field, and
`Langlands.NYLL.ClassFormation.DegreeData.GaloisSubextension.IsTotallyRamified`
(M010.056).

## Modifications

Worker 4918 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`,
   and the source import is replaced by the sibling `Definitions` port.
   `open KummerTheory` (line 19) is dropped since no such namespace is
   imported and the statements use nothing from it; `open CyclicCohomology`
   is kept.
2. Each listed `theorem` becomes a `def … : Prop` whose name adds the suffix
   `Statement`; the binders are moved before the colon and the source statement
   becomes the body. The proofs and the `@[simp]` attributes of M040.012, 013
   and 018 (lines 110, 119, 175) are omitted.
3. For M040.020, 024 and 025, whose conclusions do not mention every
   hypothesis, the definition is preceded by
   `set_option linter.unusedVariables false in`; this only silences the
   linter.
4. Each docstring is the source docstring prefixed by `Target M040.xxx:`.
5. The source module docstring (lines 9–15) is replaced by a short
   docstring recording these modifications. The unlisted source theorems
   and data commands are not stated here.

No proof is supplied: each target is to be proved separately.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
