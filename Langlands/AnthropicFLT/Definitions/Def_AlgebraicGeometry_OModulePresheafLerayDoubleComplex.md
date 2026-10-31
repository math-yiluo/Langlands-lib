# The Čech–Leray bicomplex as a bounded double complex

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`, in
namespace `AlgebraicGeometry.OModulePresheaf.Leray`. All objects live in a fixed universe `u`. The
notation is that of `Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`: `p : V' ⟶ Z`,
`πZ : Z ⟶ Spec R`, `K` an ordered affine cover of `Z` and `K'` one of `V'`.

## Definitions and results

**Čech complexes are complexes.**

- `succAbove_comp_succAbove` (theorem): for `i ≤ j` in `Fin (n+2)`,
  `succAbove j.succ ∘ succAbove i = succAbove i.castSucc ∘ succAbove j` (the simplicial identity for
  face maps).
- `res_at_eq` (theorem): restricting the values of a cochain at equal indices gives equal results.
- `d_d` and `d_d_apply` (theorems): for every presheaf of modules `F` over `π : V ⟶ Spec R` and every
  ordered affine cover `K` of `V`, the Čech differential satisfies `d ∘ d = 0`. The proof pairs the
  terms of the double sum by the simplicial identity, and paired terms have opposite signs.
- `map_iInf_fin` (theorem): preimages under a morphism commute with finite intersections of opens.

**The double complex.**

- `dV_sq`, `dH_sq` (theorems): the two differentials of the bicomplex square to zero. Through
  `biC_uncurry` and `biC_uncurry'` they are Čech differentials of `pushOpen` and `pullOpen`, so this
  follows from `d_d`.
- `dHV_comm` (theorem): `dV ∘ dH = dH ∘ dV` (restrictions commute, so the two double sums agree).
- `LerayDblCpx p πZ K K'` is the bicomplex as a `DoubleComplex.Bounded R`, with bound
  `N = max |K.ι| |K'.ι|` (by `biC_subsingleton`). `LerayDblCpx_C`, `LerayDblCpx_N`, `LerayDblCpx_dH`
  and `LerayDblCpx_dV` unfold it.
- `biAug p πZ K K' b` is the augmentation from the Čech cochains of `𝒪_{V'}` for `K'` into the column
  `a = 0`: it restricts a function on `K'.inter τ` to `K'.inter τ ∩ p⁻¹(K.U σ)` (`biAug_apply`).
- `relAug p πZ K' U` is the augmentation `Γ(V', p⁻¹(U)) → relAltC p πZ K' U 0`, restricting a function
  on `p⁻¹(U)` to each `K'.U i ∩ p⁻¹(U)` (`relAug_apply`).

**Covers of the pieces.** Assume `πZ` and `p ≫ πZ` separated.

- `rowCoverOf p πZ K K' τ`, for `τ : K'.Idx q`, is the ordered affine cover of `K'.inter τ` by the opens
  `K'.inter τ ∩ p⁻¹(K.U i)` (`rowCoverOf_U`). These are affine by `fiberAffineOpen`.
  `inter_rowCoverOf` says that its intersections are the opens `biOpen` of the bicomplex.
- `inter_restrictToPreimage` (theorem): the intersections of `restrictToPreimage p πZ K' hU` are the
  opens `K'.inter τ ∩ p⁻¹(U)`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafHom`,
  `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf` and
  `Definitions.Def_AlgebraicGeometry_DoubleComplex` are renamed to `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
