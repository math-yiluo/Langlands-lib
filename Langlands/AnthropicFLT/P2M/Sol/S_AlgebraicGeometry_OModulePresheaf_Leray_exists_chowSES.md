# The structure sheaf and the direct image along a Chow datum differ by a coherent sheaf supported off the isomorphism locus (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES`.

## Statement

`solution`: let `R` be a noetherian ring, `πZ : Z ⟶ Spec R` proper with `Z` integral, and
`D : ChowDatumProj πZ` a Chow datum (`Def_AlgebraicGeometry_ProjSpace`), with `D.p` an isomorphism over the
dense open `D.U`. Then there are a presheaf of modules `Q` over `πZ` and a short exact sequence
`0 → 𝒪_Z → relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) 0 → Q → 0` (`OModulePresheaf.SES`,
`Def_AlgebraicGeometry_OModulePresheafConstructions`) such that `Q` is coherent, quasi-coherent and supported
in the complement of `D.U`. The middle term is the zeroth relative Čech cohomology presheaf, i.e.
`D.p_* 𝒪_{D.V'}`. The theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES`
states this as `AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf`.

1. **General helpers** (section `General`). `Hom.symmOfBijective` inverts a morphism of presheaves of modules
   that is bijective on every open (`Hom.symmOfBijective_bijective`). These two declarations are private, as
   in FLT. `isQuasicoherent_unit` says the structure presheaf `unit π` is quasi-coherent (sections over a
   basic open of an affine are a localization).
2. **The comparison map** (section `UnitToPullOpen`). `unitToPullOpen p πZ` is the morphism
   `𝒪_Z → pullOpen p πZ ⊤`, `s ↦ p^*(s)` on `Γ(V', p⁻¹(U))` (`unitToPullOpen_app`).
3. **Chow data** (section `Chow`). Over an open `W ≤ D.U`, the restriction of `D.p` is an isomorphism
   (`chow_restrict_isIso`), so `Γ(Z, W) → Γ(D.V', D.p⁻¹(W))` is bijective (`chow_appLE_bijective_of_le_U`).
   `unitToPullOpen_injective_chow`: on every open `U`, the comparison map is injective, because a section
   killed by `D.p^*` vanishes on `U ∩ D.U`, and on the integral scheme `Z` restriction to a nonempty open is
   injective.
4. **The sequence** (`exists_chowSES'`). By `OModulePresheaf.Leray.exists_hom_relHPresheaf_zero`, the zeroth
   relative cohomology presheaf is isomorphic to `pullOpen D.p πZ ⊤`. Composing gives an injective
   `χ : 𝒪_Z → relHPresheaf … 0`, and `Q = coker χ`; the sequence consists of `χ` and the projection of `imCokerSES χ`. `Q` is
   coherent and quasi-coherent by `OModulePresheaf.isCoherent_coker` and
   `OModulePresheaf.isQuasicoherent_coker`, applied with `OModulePresheaf.Leray.isCoherent_relHPresheaf_chow`,
   `OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow` and `isQuasicoherent_unit`. On an affine open
   `W ≤ D.U` the map `χ` is surjective by `chow_appLE_bijective_of_le_U`, so `Q` vanishes there.

As in FLT, the file removes some instances and simp lemmas for the rest of the file (`attribute [-instance]`
and `attribute [-simp]`).

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCover`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow` are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. Each `p2m_open_scoped "N" in` becomes
  `open scoped _root_.N in`. No declaration, statement or proof step changed.
