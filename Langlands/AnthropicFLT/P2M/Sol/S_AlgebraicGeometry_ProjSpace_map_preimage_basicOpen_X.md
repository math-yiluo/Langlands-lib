# The base-change map of projective spaces pulls back the standard charts to the standard charts (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X`. Its only
declaration is `P2MW.S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X.solution`.

## Statement

`solution`: for commutative rings `R`, `A` with `[Algebra R A]`, `n : ℕ` and `j : Fin (n + 1)`, the preimage
under `ProjSpace.map R A n : ℙⁿ_A ⟶ ℙⁿ_R` (`Def_AlgebraicGeometry_ProjSpace`) of the standard chart `D₊(Xⱼ)`
of `ℙⁿ_R` is the standard chart `D₊(Xⱼ)` of `ℙⁿ_A`. The theorem module
`Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` states this as
`AlgebraicGeometry.ProjSpace.map_preimage_basicOpen_X` and proves it from `solution`.

## Proof outline

Unfold `ProjSpace.map` (`ProjSpace.map_eq`) to the morphism of `Proj`s induced by the graded map
`R[X₀, …, Xₙ] → A[X₀, …, Xₙ]`. Mathlib's `Proj.map_preimage_basicOpen` says the preimage of `D₊(s)` is `D₊` of
the image of `s`, and the image of `Xⱼ` is `Xⱼ` (`MvPolynomial.map_X`).

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_ProjSpace` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands.
