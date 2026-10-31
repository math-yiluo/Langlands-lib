# The filtration of a presheaf of modules by powers of an ideal sheaf

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration`, in
namespace `AlgebraicGeometry.OModulePresheaf`. All objects live in a fixed universe `u`. Throughout,
`π : V ⟶ Spec R` for a commutative ring `R`, `I` is an ideal sheaf on `V` (`V.IdealSheafData`) and `F`
is a presheaf of modules over `π` (`OModulePresheaf π`).

## Definitions and results

**The ideal on arbitrary opens.**

- `IdealAnnihilates π I F` means that on every affine open `U`, every element of the ideal `I(U)`
  annihilates `F(U)`.
- `idealSections I U`, for any open `U`, is the kernel of `Γ(V, U) → Γ(Z, Z ∩ U)` for the closed
  subscheme `Z` of `I`. On affine opens it equals `I(U)` (`idealSections_eq_ideal`). It is preserved by
  restriction, and so are its powers (`idealSections_res`, `idealSections_pow_res`).

**The filtration.**

- `idealPowSub π I F k U` is the `R`-submodule `(idealSections I U)ᵏ · F(U)` of `F(U)`. It is preserved
  by restriction (`idealPowSub_res`), decreasing in `k` (`idealPowSub_antitone`), stable under
  `Γ(V, U)` (`idealPowSub_smul_mem`), all of `F(U)` for `k = 0` (`idealPowSub_zero`), and on affine
  opens it is `I(U)ᵏ · F(U)` (`mem_idealPowSub_iff_of_affine`).
- `idealPow π I F k` is the presheaf of modules `U ↦ Iᵏ F(U)`.
- `idealPowSuccSub π I F k U` is `Iᵏ⁺¹ F(U)` viewed inside `Iᵏ F(U)`, and `idealPowQuot π I F k` is the
  quotient presheaf `U ↦ Iᵏ F(U) / Iᵏ⁺¹ F(U)`, with the induced `Γ(V, U)`-module structure
  (`idealPowQuotModuleSections`, `idealPowQuot_smul_mk`).
- `idealPowSuccInc π I F k` is the inclusion `Iᵏ⁺¹ F → Iᵏ F` on affine opens, and
  `idealPowSES π I F k` is the affine short exact sequence
  `0 → Iᵏ⁺¹ F → Iᵏ F → Iᵏ F / Iᵏ⁺¹ F → 0`.
- `idealAnnihilates_idealPowQuot` (theorem): `I` annihilates every graded piece `Iᵏ F / Iᵏ⁺¹ F`.
- `idealPowZeroSES π I F` is the affine short exact sequence `0 → 0 → I⁰ F → F → 0`, expressing
  `I⁰ F = F`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OModulePresheafIdealFiltration.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` is
  renamed to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
