# Covers of a scheme by two affine opens

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`, in namespace
`AlgebraicGeometry`. All schemes and rings live in a fixed universe `u`.

## Definitions

- A `Scheme.TwoAffineOpenCover X` is a pair of affine opens `U0`, `U1` of the scheme `X` with
  `U0 ⊔ U1 = ⊤` whose intersection `U0 ⊓ U1` is also affine.
- `specMap R A`, for an `R`-algebra `A`, is the morphism `Spec A ⟶ Spec R` induced by the algebra map.

Let `c : X ⟶ Spec R` for a commutative ring `R`.

- `algebraOfHom c U` is the `R`-algebra structure on `Γ(X, U)` given by `c`: the composite of
  `R ≅ Γ(Spec R, ⊤)` with `c.appLE ⊤ U`. `algebraMap_algebraOfHom` records its algebra map.
- `restrictAlgHom c h`, for opens `V ≤ U`, is the restriction `Γ(X, U) → Γ(X, V)` as a map of
  `R`-algebras for these structures.
- For a two-affine cover `𝒱`, `𝒱.cover c` is the two-chart cover (`TwoChartCech.Cover R`) with
  `A0 = Γ(X, U0)`, `A1 = Γ(X, U1)`, `A01 = Γ(X, U0 ⊓ U1)` and the restriction maps to the overlap.
  `𝒱.structureSheafSections c` is its structure-sheaf sections datum, and
  `𝒱.lineBundleSections c t`, for a unit `t` of `Γ(X, U0 ⊓ U1)`, the line bundle with transition
  function `t`.
- `𝒱.toH0 c : Γ(X, ⊤) → H0` is the `R`-linear map sending a global function `s` to the pair of its
  restrictions to `U0` and `U1`. It lands in the `H0` of the structure-sheaf sections
  (`restrict_mem_H0`).
- `𝒱.pullback c A`, for an `R`-algebra `A`, is the two-affine cover of the fibre product
  `X ×_{Spec R} Spec A` by the preimages of `U0` and `U1` under the first projection. It is a cover by
  affine opens because the projection is an affine morphism (`isAffineHom_fst`).

The remaining declarations are unfolding lemmas (`cover_A0`, `cover_A1`, `cover_A01`, `cover_ρ0_apply`,
`cover_ρ1_apply`, `toH0_apply_coe`, `pullback_U0`, `pullback_U1`) and `res_res`, which says that
restricting twice equals restricting once.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_TwoAffineOpenCover.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_TwoChartCech` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
