# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.solution ι₀ A ι g hpb hcomp d Θ₀ hΘ₀ r hfin hproj hrank hgen`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.ProjSpace.finite_projective_H0_twist_of_ker_baseChange_of_isPullback`: let
`Z ⊆ ℙⁿ_A` be the base change of `Z₀ ⊆ ℙⁿ_{A₀}` along `A₀ → A`, `d ∈ ℕ`, and `Θ₀` the dehomogenization map
from forms of degree `d` over `A₀` to `0`-cochains of `𝒪_{Z₀}(d)`. Suppose that the kernel of the base
change to `A` of the first Čech differential of `𝒪_{Z₀}(d)` is finite projective of constant rank `r` and
contained in the image of `Θ₀ ⊗ A`. Then `H⁰(Z, 𝒪_Z(d))` (Čech) is finite projective of constant rank `r`,
and every class in it is given in the charts by a form of degree `d` over `A`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.ProjSpace.finite_projective_H0_twist_of_ker_baseChange_of_isPullback`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback` (same contribution).
Other imports: `Mathlib`.
