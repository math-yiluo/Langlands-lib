# Two-chart Čech data of a sheaf of modules on a scheme

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf`, in namespace
`AlgebraicGeometry.Scheme.TwoAffineOpenCover`. All objects live in a fixed universe `u`.

## Definitions

Let `c : X ⟶ Spec R` for a commutative ring `R`, and let `M` be a sheaf of `𝒪_X`-modules
(`X.Modules`).

- `moduleSectionsOfHom c M U` is the `R`-module structure on the sections `Γ(M, U)` obtained by
  restricting scalars along `R → Γ(X, U)` (the algebra structure `algebraOfHom c U`).
  `isScalarTower_sections` says that the `R`-, `Γ(X, U)`- and `Γ(M, U)`-actions form a scalar tower.
- `restrictSections c M h`, for opens `V ≤ U`, is the restriction map `Γ(M, U) → Γ(M, V)` as an
  `R`-linear map (`restrictSections_apply`).
- `𝒱.sectionsOf c M`, for a cover `𝒱` of `X` by two affine opens `U0`, `U1`, is the two-chart sections
  datum (`TwoChartCech.Sections (𝒱.cover c)`) with `M0 = Γ(M, U0)`, `M1 = Γ(M, U1)`,
  `M01 = Γ(M, U0 ⊓ U1)` and the restriction maps to the overlap.

The lemmas `sectionsOf_M0`, `sectionsOf_M1`, `sectionsOf_M01`, `sectionsOf_r0_apply` and
`sectionsOf_r1_apply` unfold `sectionsOf` (all by `rfl`).

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_TwoChartCechSectionsOf.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
