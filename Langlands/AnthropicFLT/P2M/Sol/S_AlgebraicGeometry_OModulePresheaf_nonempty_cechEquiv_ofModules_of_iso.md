# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry _root_.Opposite`: namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry` dropped.
- 3 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.AlgebraicGeometry.OModulePresheaf.IsoTransfer (cechFinite_iff)` is dropped; see the port edit below.
- Port edit replacing a `P2M.Util` alias (FLT line 131, line 141 here): `⟨⟨H0Equiv (ofIso (π := π) e) K⟩, fun i => ⟨HSuccEquiv (ofIso (π := π) e) K i⟩, cechFinite_iff (ofIso (π := π) e) K⟩` is replaced by `⟨⟨H0Equiv (ofIso (π := π) e) K⟩, fun i => ⟨HSuccEquiv (ofIso (π := π) e) K i⟩, _root_.AlgebraicGeometry.OModulePresheaf.IsoTransfer.cechFinite_iff (ofIso (π := π) e) K⟩`. FLT `p2m_export "AlgebraicGeometry.OModulePresheaf.IsoTransfer" "cechFinite_iff"` aliases the private declaration(s) `_root_.AlgebraicGeometry.OModulePresheaf.IsoTransfer.`, `_root_.cechFinite_iff.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `AlgebraicGeometry.OModulePresheaf.IsoTransfer` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso`. Statement. `AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso`: an isomorphism `M ≅ M'` of modules on
`V` induces isomorphisms of the Čech cohomology groups `H⁰` and `Hⁱ⁺¹` of their FLT presheaves for every
ordered affine cover, and `M` has finite-dimensional Čech cohomology iff `M'` does.

Proof (namespace `AlgebraicGeometry.OModulePresheaf.IsoTransfer`). `LinIso F G`: compatible linear
isomorphisms on all opens; they induce isomorphisms of cochains commuting with the differentials
(`cochainEquiv`, `d_cochainEquiv`), of cocycles (`map_ker`, `kerEquiv`) and of coboundaries
(`map_boundaries`), hence `H0Equiv` and `HSuccEquiv` (and `cechFinite_iff`). `ofIso e`: an isomorphism of
modules gives such a family (naturality of `e` with respect to restrictions).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.LinIso`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.cochainEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.cochainEquiv_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.d_cochainEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.d_comp_cochainEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.map_ker`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.H0Equiv`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.kerEquiv`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.kerEquiv_apply_coe`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.map_boundaries`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.HSuccEquiv`
- private theorem `AlgebraicGeometry.OModulePresheaf.IsoTransfer.cechFinite_iff`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.AlgebraicGeometry.OModulePresheaf.IsoTransfer.ofIso`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library).
Other imports: none.
