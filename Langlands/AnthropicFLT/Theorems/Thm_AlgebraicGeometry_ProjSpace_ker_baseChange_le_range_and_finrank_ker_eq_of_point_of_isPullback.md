# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.solution ι₀ K ιK e hpb hcomp d Θ₀ hΘ₀ h q hq ha hb`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.ProjSpace.ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback`: let
`Z_K ⊆ ℙⁿ_K` be the base change of `Z₀ ⊆ ℙⁿ_{A₀}` to a field `K`, `d ∈ ℕ`, `Θ₀` the dehomogenization map of
`Z₀` in degree `d`, and `q` a point over `K` with Hilbert function `h` whose forms of degree `d` are those
vanishing on `Z_K`. If the higher Čech cohomology of `𝒪_{Z_K}(d)` vanishes and every `H⁰` class comes
from a form, then after base change to `K` the Čech complex of `𝒪_{Z₀}(d)` is exact in positive
degrees, the kernel of the first differential lies in the image of `Θ₀ ⊗ K`, and this kernel has
dimension `h d`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.ProjSpace.ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback` (same contribution).
Other imports: `Mathlib`.
