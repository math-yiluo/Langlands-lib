# The Čech–Leray bicomplex of a morphism and relative Čech cohomology presheaves

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`, in
namespace `AlgebraicGeometry.OModulePresheaf.Leray`. All objects live in a fixed universe `u`.
Throughout, `p : V' ⟶ Z` and `πZ : Z ⟶ Spec R` for a commutative ring `R`, `K` is an ordered affine
cover of `Z` and `K'` an ordered affine cover of `V'`. Sections of `V'` carry the `R`-module structure
given by `p ≫ πZ` (`OrderedAffineCoverOf.moduleSections`).

## Definitions and results

**Affine pieces over affine opens.**

- `Scheme.OrderedAffineCover.fiberAffineOpen` (theorem): if `πZ` is separated, `W ⊆ V'` and `U ⊆ Z`
  are affine opens, then `W ∩ p⁻¹(U)` is affine. It is identified with the fibre product
  `W ×_Z U`, which is affine because it is a closed subscheme of `W ×_{Spec R} U`.
- `restrictToPreimage p πZ K' hU`, for an affine open `U` of `Z`, is the ordered affine cover of
  `p⁻¹(U)` by the opens `K'.U i ∩ p⁻¹(U)` (`restrictToPreimage_U`).

**The bicomplex.** For degrees `a, b ∈ ℕ`:

- `HIdx K a = K.Idx a` and `VIdx K' b = K'.Idx b` are the index tuples, and `BiIdx K K' a b` their
  product;
- `biOpen p K K' a b σ τ` is the open `K'.inter τ ∩ p⁻¹(K.inter σ)` of `V'`;
- `biC p πZ K K' a b` is the `R`-module of functions on these opens: the product of `Γ(V', biOpen σ τ)`
  over all `(σ, τ)`;
- `dH a b : biC a b → biC (a+1) b` is the Čech differential in the `K` direction and
  `dV a b : biC a b → biC a (b+1)` the Čech differential in the `K'` direction, each an alternating
  sum of restrictions (`dH_apply`, `dH_apply'`, `dV_apply`, `dV_apply'`);
- `biC_subsingleton` (theorem): `biC a b` is trivial as soon as `a` or `b` is at least the larger of
  the two cover sizes, because then there are no strictly increasing index tuples.

**Relative Čech cohomology as a presheaf on `Z`.** For an open `U` of `Z` and `b ∈ ℕ`:

- `relAltC p πZ K' U b` is the Čech cochain module of `p⁻¹(U)` for the cover `K'`: the product of
  `Γ(V', K'.inter τ ∩ p⁻¹(U))` over `τ : K'.Idx b`; `relAltd` is its Čech differential
  (`relAltd_apply'`), and `relAltH p πZ K' U b` its cohomology (coboundaries `relAltHB`, zero for
  `b = 0`).
- `pushOpen p πZ U` is the presheaf of modules `W ↦ Γ(V', W ∩ p⁻¹(U))` over `p ≫ πZ`, and
  `relAltd_eq_d` says that `relAltd` is its Čech differential for `K'`.
- `pullOpen p πZ W`, for an open `W` of `V'`, is the presheaf of modules `U ↦ Γ(V', W ∩ p⁻¹(U))`
  over `πZ`, with `Γ(Z, U)` acting through `p`.
- Through `pullOpen`, the modules `relAltC`, the cocycles of `relAltd` and `relAltH` become
  `Γ(Z, U)`-modules compatibly with `R` (instances `relAltC_modΓ`, `relAltC_scalarTower`,
  `ker_relAltd_smul`, `ker_relAltd_modΓ`, `relAltH_smul`, `relAltH_modΓ`, `relAltH_scalarTower`).
  `relAltd_Γsmul` and `relAltHB_Γsmul` (theorems) say that the differential is `Γ(Z, U)`-linear and the
  coboundaries are `Γ(Z, U)`-stable.
- `relRes p πZ K' h b`, for opens `U ≤ U'` of `Z`, restricts cochains from `p⁻¹(U')` to `p⁻¹(U)`
  (`relRes_apply`). It commutes with the differentials (`relRes_comm`) and so induces `relResKer` on
  cocycles (`relResKer_coe`), preserving coboundaries (`relAltHB_res_le`).
- `relHPresheaf p πZ K' b` is the presheaf of modules `U ↦ relAltH p πZ K' U b` over `πZ`: the `b`-th
  relative Čech cohomology of `p` for the cover `K'`. It plays the role of the higher direct image
  `Rᵇ p_* 𝒪_{V'}`.

**Rows and columns of the bicomplex.**

- `biC_uncurry p πZ K K' a b` is the `R`-linear isomorphism between `biC a b` and the product over
  `σ : K.Idx a` of `relAltC p πZ K' (K.inter σ) b`. `dV_uncurry` (theorem) says it carries `dV` to
  `relAltd` on each factor. So each column of the bicomplex is a relative Čech complex.
- `biC_uncurry'` is the isomorphism between `biC a b` and the product over `τ : K'.Idx b` of the Čech
  cochains of `pullOpen p πZ (K'.inter τ)` for `K`. `dH_uncurry` (theorem) says it carries `dH` to the
  Čech differential `OModulePresheaf.d`. So each row is a Čech complex on `Z`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OModulePresheafLerayBicomplex.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` and
  `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf` are renamed to
  `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
