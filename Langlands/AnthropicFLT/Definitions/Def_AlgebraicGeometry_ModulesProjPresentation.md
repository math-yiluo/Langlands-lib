# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_ModulesProjPresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Presentations of a module by sections giving a morphism to projective space (namespaces
`AlgebraicGeometry.Scheme.Modules` and `AlgebraicGeometry.ProjSpace`), for `f : X ⟶ Spec R`.

- `ProjPresentation M f N` (a structure): global sections `σ₀, …, σ_N` of the module `M`, a morphism
  `toProj : X ⟶ ℙᴺ_R` (FLT's `Proj` of the standard graded polynomial ring) over `Spec R`
  (`toProj_π`), such that on every open `V` inside the preimage of the standard chart `D₊(Xᵢ)` the map
  `g ↦ g · σᵢ|_V` from `Γ(X, V)` to `Γ(M, V)` is bijective (`frame`: `σᵢ` is a basis of `M` there),
  and on the preimage of `D₊(Xᵢ)` the pullback of the chart coordinate `Xⱼ/Xᵢ`
  (`ProjSpace.ratio R N i j`) times `σᵢ` is `σⱼ` (`app_ratio_smul`).
- `FiniteBySections M f`: some presentation has `toProj` finite. `ClosedImmersionBySections M f`:
  some presentation has `toProj` a closed immersion.
- `ProjSpace.awayZeroEval R`: the ring map from the degree-zero localization of `R[X₀]` at `X₀` to
  `R` (evaluation at `X₀ = 1`); `ProjSpace.pointOfProjZero R : Spec R ⟶ ℙ⁰_R`, the resulting
  morphism into the chart, with `pointOfProjZero_π` (a section of `ℙ⁰_R ⟶ Spec R`) and
  `pointOfProjZero_preimage_basicOpen` (it lands in `D₊(X₀)`).
- `Scheme.Modules.unitOne X`: the global section `1` of the structure sheaf;
  `ProjPresentation.unitSpec R`: the presentation of the structure sheaf of `Spec R` over
  `𝟙 (Spec R)` with `N = 0`, `σ₀ = 1` and `toProj = pointOfProjZero R`.

## Declarations

Names, namespaces and statements are the FLT ones.

- structure `AlgebraicGeometry.Scheme.Modules.ProjPresentation`
- def `AlgebraicGeometry.Scheme.Modules.FiniteBySections`
- def `AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections`
- def `AlgebraicGeometry.ProjSpace.awayZeroEval`
- def `AlgebraicGeometry.ProjSpace.pointOfProjZero`
- theorem `AlgebraicGeometry.ProjSpace.pointOfProjZero_π`
- theorem `AlgebraicGeometry.ProjSpace.pointOfProjZero_preimage_basicOpen`
- def `AlgebraicGeometry.Scheme.Modules.unitOne`
- def `AlgebraicGeometry.Scheme.Modules.ProjPresentation.unitSpec`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library).
Other imports: `Mathlib`.
