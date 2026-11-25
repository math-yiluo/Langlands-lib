# The dual of an invertible sheaf is invertible and inverse to it

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2` proves the theorem `AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2`.

## Statement

Let `X` be a scheme and `L` an invertible sheaf of modules on `X` (the port's
`Scheme.Modules.IsInvertibleFLT`: locally isomorphic to the structure sheaf).
Use the monoidal closed structure on `X.Modules` of the FLT modules
`Definitions/Def_SheafOfModules_Monoidal` and `Def_SheafOfModules_MonoidalV2`:
the tensor product is the sheafification of the tensor product of presheaves
of modules, and `Scheme.Modules.dualFLT L` is the internal hom from `L` to the
unit `𝟙_ X.Modules` (the structure sheaf). Then `dualFLT L` is invertible and
`L ⊗ dualFLT L ≅ 𝟙_ X.Modules`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's, apart from the renames described under “Names changed by the Library” below. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`);
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2`, which has the same statement. The Markdown of that module outlines the argument.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- its uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.dual` are uses of `IsInvertibleFLT`, `dualFLT` now.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
