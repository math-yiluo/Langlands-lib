# The zeroth relative Čech cohomology presheaf is the direct image of the structure sheaf (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero`. Its
declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero`.

## Statement

`solution`: for `p : V' ⟶ Z`, `πZ : Z ⟶ Spec R` and an ordered affine cover `K'` of `V'`, there is a morphism
of presheaves of modules `φ : relHPresheaf p πZ K' 0 ⟶ pullOpen p πZ ⊤` (`OModulePresheaf.Hom`;
`Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`, `Def_AlgebraicGeometry_OModulePresheafHom`) from the
zeroth relative Čech cohomology presheaf to the presheaf `U ↦ Γ(V', p⁻¹(U))`, i.e. the direct image
`p_* 𝒪_{V'}`, such that

- `φ.app U` is bijective for every open `U` of `Z`, and
- composing `φ.app U` with the augmentation `relAug p πZ K' U` sends the class of a `0`-cocycle `x` back to
  `x`.

The theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero` states
this as `AlgebraicGeometry.OModulePresheaf.Leray.exists_hom_relHPresheaf_zero` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray.RelHZero`.

1. **Gluing.** `res_res`, `res_self`, `idx_zero_ext` and `inter_zero` handle restrictions and `0`-indices
   (`K'.inter σ = K'.U (σ 0)`). The opens `K'.U i ∩ p⁻¹(U)` cover `p⁻¹(U)` (`relCover_le`). `ker_relAltd_zero`
   says the relative `0`-cocycles over `U` are exactly the images of the augmentation `relAug`: a cocycle
   agrees on pairwise overlaps (the cocycle condition on the index `![a, b]`), so the sheaf property of
   `𝒪_{V'}` glues it to a section on `p⁻¹(U)`. `relAug_injective` holds because these opens cover `p⁻¹(U)`.
2. **The isomorphism.** In degree `0` the cohomology is the cocycles, so `toRelH` (the augmentation viewed as
   a map to `relAltH … 0`) is bijective (`toRelH_bijective`), `Γ(Z, U)`-linear (`toRelH_smul`) and compatible
   with restriction (`toRelH_res`). Its inverse is `relHEquiv` (`toRelH_relHEquiv`, `relHEquiv_toRelH`).
3. **The morphism of presheaves.** `relHZeroHom` assembles the inverses `relHEquiv U` into an
   `OModulePresheaf.Hom` (`relHZeroHom_app`), and `relAug_relHZeroHom_mk` is the second property. `solution`
   is `⟨relHZeroHom, bijectivity, relAug_relHZeroHom_mk⟩`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed
under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex` is
  renamed to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.
