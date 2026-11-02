# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback`. Statement. `AlgebraicGeometry.ProjSpace.finite_projective_H0_twist_of_ker_baseChange_of_isPullback`: let
`Z ⊆ ℙⁿ_A` be the base change of `Z₀ ⊆ ℙⁿ_{A₀}` along `A₀ → A`, `d ∈ ℕ`, and `Θ₀` the dehomogenization map
from forms of degree `d` over `A₀` to `0`-cochains of `𝒪_{Z₀}(d)`. Suppose that the kernel of the base
change to `A` of the first Čech differential of `𝒪_{Z₀}(d)` is finite projective of constant rank `r` and
contained in the image of `Θ₀ ⊗ A`. Then `H⁰(Z, 𝒪_Z(d))` (Čech) is finite projective of constant rank `r`,
and every class in it is given in the charts by a form of degree `d` over `A`.

Proof. Section `Setup`: base-change compatibility of the charts and frame units along
`ProjSpace.map` (`toB`, `toB_ratio`, `restrictFun_app_frameUnit`, `preimage_inter`). Section `Theta`:
dehomogenization `chartVal` and `exists_theta`. Section `KerEquiv`: the ported
`ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback` identifies the Čech complex of `Z`
with the base change of that of `Z₀`, so `H⁰` of `Z` is isomorphic to the kernel of the base-changed
differential (`exists_kerEquiv`); finiteness, projectivity and rank transfer along this isomorphism,
and the hypothesis on `Θ₀ ⊗ A` gives the forms.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.preimage_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.preimage_inter`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.X_eq_mvMapGraded_mul_one`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.one_mem_zero`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.toB`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.toB_ratio`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.restrictFun_app_pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.restrictFun_app_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.restrictFun_app_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.toB_mkDeg`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.chartVal`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.isHomogeneous_of_mem`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.vertex`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.chart_le_inter_vertex`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.exists_theta`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.K4ISol.exists_kerEquiv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` (same contribution).
Other imports: `Mathlib`.
