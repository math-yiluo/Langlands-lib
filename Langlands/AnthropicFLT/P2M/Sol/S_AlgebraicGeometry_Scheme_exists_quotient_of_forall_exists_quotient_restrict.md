# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`

Ported by Worker 934 for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (finite étale subgroup
quotients of projectively embedded abelian schemes). Proof module (FLT `P2M/Sol/`): local
finite locally free quotients over an invariant open cover glue to a global quotient.

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean` (SHA-256
`ed8eabef91f11b0b5aeceedfa01b9389f1117d1f93ed5c416e88240042262ebe`) from the Anthropic Lean
formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`;
project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at
6e837e75355538c7f80bab5b956861e86c4eacc2", literature id
`anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the
changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT
`LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Theorems.*`) are renamed to `Langlands.AnthropicFLT.*`; the
  Mathlib import is unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 5 `p2m_open "…"` commands (an FLT command from `P2M.Util` that opens the named namespaces
  and activates their scoped extensions; it does not check that a namespace exists) are
  replaced by standard `open _root_.N₁ _root_.N₂ …` commands with the same namespaces. In
  the first one, the namespace
  `P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.AlgebraicGeometry`
  is dropped: it does not exist at that point of the file, and standard `open` rejects it
  (`unknown namespace`); the file compiles without it.
- 11 `p2m_export "N" "a b …"` commands (an FLT command from `P2M.Util` that adds aliases `a`,
  `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by
  `export _root_.N (a b …)` with the same names.
- 19 `p2m_reactivate "N₁ N₂ …"` commands (an FLT command from `P2M.Util` that re-activates
  the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces)
  are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which
  activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text. With the
  project Mathlib it compiles without errors; the `haveI` style linter warns once.

## Content

The file works in the FLT namespace
`P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`, inside
copies `AlgebraicGeometry`, `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.GlueData`
of the Mathlib namespaces (the `export` commands make the Mathlib names visible there).

- `GlueData.MkCore` (structure) and its namespace: a lighter interface for gluing schemes.
  Data are schemes `U i`, opens `V i j ⊆ U i` with `V i i = ⊤`, transition maps
  `t i j : V i j ⟶ V j i` with `t i i = 𝟙`, the inclusion condition `t_inter` and a cocycle
  condition stated on triple overlaps. From these, `t_inv` shows `t i j ≫ t j i = 𝟙`, and
  `glueData` builds a Mathlib `Scheme.GlueData`; the `glueData_*` simp lemmas, `t_ι_ι` and
  `preimage_opensRange` describe it.
- Section `Saturation`: for `p` flat and locally of finite presentation (hence open) with
  `IsPullback s t p p`, the image `imageOpens O` of an `R`-invariant open `O` is open and
  `p⁻¹(p(O)) = O` (`preimage_image_eq`, `preimage_imageOpens`).
- Section `RestrictPkg`: `restrict_pkg` restricts a finite locally free quotient `p` over an
  open `U` of the target, using the ported base change theorem
  `AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback`.
- Section `Compare`: `quotIso` is the isomorphism between two coequalizers of isomorphic
  parallel pairs, and `π_quotIso_hom` its compatibility.
- Section `Main`: the hypotheses are `W : X → X.Opens` with `x ∈ W x` and
  `s⁻¹(W x) = t⁻¹(W x)`, and `loc`, a local quotient `ploc x : W x ⟶ Yloc x` for each `x`.
  `V x y ⊆ Yloc x` is the image of `W x ∩ W y`; by saturation its preimage is exactly
  `W x ∩ W y` (`preimage_V`). The restrictions `pV x y` of `ploc x` over `V x y` are
  coequalizers (`coeqV`) of the restricted relation on `W x ∩ W y`. Comparing the
  restricted relations through `W x` and through `W y` (`eX`, `eR`, `hs_comm`, `ht_comm`)
  gives isomorphisms `φ x y : V x y ≅ V y x` with `pV x y ≫ φ x y = eX ≫ pV y x`.
- Section `Core`: `core` is the `MkCore` with `U = Yloc`, `V`, `t = φ`. Its inclusion
  (`core_t_inter`) and cocycle (`core_cocycle`) conditions are checked after composing with
  the epimorphisms `pV`, where they reduce to identities of open immersions into `X`.
- Section `Main56`: `D` is the glued scheme. The charts `ploc x ≫ D.ι x` agree on overlaps
  (`chart_comp_eq`), so they glue along the open cover `coverW` of `X` to
  `pglued : X ⟶ D.glued` (`ι_pglued`). It satisfies `s ≫ pglued = t ≫ pglued`
  (`s_pglued`), and over each chart `D.ι x` it is the pullback of `ploc x`
  (`preimage_chart`, `isPullback_chart`). Being finite, flat, locally of finite presentation
  and surjective are local on the target, so `pglued` has them (`isFinite_pglued`,
  `flat_pglued`, `lfp_pglued`, `surjective_pglued`). `isPullback_pglued` checks
  `IsPullback s t pglued pglued` on the open cover `coverW`, pasting `loc` with
  `isPullback_chart`. `main` adds the coequalizer property: `pglued` is an effective
  epimorphism (quasi-compact, flat and surjective), hence the coequalizer of its kernel pair.
- `solution` restates `main`.

This is the gluing step of the proof of Stacks Proposition 66.14.1 (Tag 07S6), which glues
the affine quotients `U_i/R_i` along the images of the overlaps `U_i ∩ U_j`.

## Declarations

Names, namespaces and statements are the FLT ones. All declarations below are in the FLT
namespace `P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`,
except the private definitions `V` and `core`, whose FLT declarations carry the root names
`_root_.AlgebraicGeometry.Scheme.QuotGlue.V` and `_root_.AlgebraicGeometry.Scheme.QuotGlue.core`
and are exported into the FLT namespace.

In `AlgebraicGeometry.Scheme.GlueData`:

- structure `MkCore`
- in `MkCore`: abbrev `W`, `τ`, `σ`, `isoW`; def `t'`, `glueData`; lemma `σ_hom_ι_ι`,
  `σ_hom_σ_hom`, `σ_self_hom_ι`, `τ_ι`, `cocycle'`, `W_self`, `t_inv`, `core`,
  `glueData_J`, `glueData_U`, `glueData_V`, `glueData_f`, `glueData_t`, `t_ι_ι`,
  `preimage_opensRange`; three anonymous scoped instances (`IsIso` of `(W i j i).ι` and of
  `t i j`, `IsOpenImmersion` of `glueData.ι i`)

In `AlgebraicGeometry.Scheme.QuotGlue`:

- section `Saturation`: lemma `preimage_image_eq`, `isOpen_image`, `coe_imageOpens`,
  `preimage_imageOpens`, `imageOpens_top`, `le_imageOpens_iff`; def `imageOpens`
- section `RestrictPkg`: lemma `preimage_preimage_eq`, `tRes_ι`, `sRes_w`; def `tRes`;
  theorem `restrict_pkg`
- section `Compare`: def `quotIso`; lemma `π_quotIso_hom`
- section `Main`: abbrev `tW`, `pV`; def `Yloc`, `ploc`, `coeqV`, `eX`, `eR`, `φ`; private
  def `V` (root name, see above); lemma `tW_ι`, `ploc_spec`, `inv_overlap`, `preimage_V`, `range_overlap`,
  `hw`, `hpb`, `isPullback_V`, `eX_hom_ι`, `sres_preimage`, `range_roverlap`, `eR_hom_ι`,
  `hs_comm`, `ht_comm`, `pV_φ_hom`, `V_self`, `eX_self`, `φ_self`; four anonymous scoped
  instances for `ploc` and scoped instance `epi_pV`
- section `Core`: scoped instance `isFinite_pV`, `flat_pV`, `lfp_pV`, `surj_pV`,
  `epi_pV_restrict`; lemma `ι_mem_preimage_V`, `core_t_inter`, `core_cocycle`, `core_J`,
  `core_U`, `core_V`, `core_t`; private def `core` (root name, see above)
- section `Main56`: abbrev `D`, `chart`; def `coverW`, `liftOverlap`, `pglued`, `ιY`;
  lemma `coverW_f`, `liftOverlap_ι`, `chart_comp_eq`, `ι_pglued`, `s_pglued`,
  `preimage_chart`, `ιY_def`, `isPullback_chart`, `isFinite_pglued`, `flat_pglued`,
  `lfp_pglued`, `surjective_pglued`, `isPullback_pglued`; scoped instance
  `isOpenImmersion_ιY`; theorem `main`

At the top of the FLT namespace:

- theorem `solution`

## Dependencies

Ported FLT modules imported:
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback`.
All modules also import `Mathlib`.
