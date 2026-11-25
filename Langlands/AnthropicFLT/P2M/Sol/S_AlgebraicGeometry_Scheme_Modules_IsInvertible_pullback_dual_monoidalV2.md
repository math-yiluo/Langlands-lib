# Pullback commutes with the dual of an invertible sheaf

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2` states under its FLT name.

## Statement

Let `f : X ⟶ Y` be a morphism of schemes and `L` an invertible sheaf of
modules on `Y` (the port's `Scheme.Modules.IsInvertibleFLT`). Write
`Scheme.Modules.dualFLT L` for the internal hom from `L` to the structure sheaf
(`Definitions/Def_SheafOfModules_Monoidal`). Then the pullback of the dual
of `L` is isomorphic to the dual of the pullback of `L`:
`Nonempty (f^* (dualFLT L) ≅ dualFLT (f^* L))`.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's, apart from the renames described under “Names changed by the Library” below. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`);
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names); a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

The module first proves a general uniqueness of inverses: in a braided
monoidal category, if `e : L ⊗ M ≅ 𝟙` and `e' : L ⊗ M' ≅ 𝟙`, then
`M ≅ M'` (`inverseUnique`), by the chain
`M ≅ 𝟙 ⊗ M ≅ (L ⊗ M') ⊗ M ≅ (M' ⊗ L) ⊗ M ≅ M' ⊗ (L ⊗ M) ≅ M' ⊗ 𝟙 ≅ M'`
of unitors, `e'`, the braiding, the associator and `e`.

By `AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_monoidalV2`,
`L ⊗ dualFLT L ≅ 𝟙`, and, since `f^* L` is again invertible
(`IsInvertible.pullbackFLT`), `f^* L ⊗ dualFLT (f^* L) ≅ 𝟙`. Pullback is a
monoidal functor (`Functor.Monoidal.μIso`), so the first isomorphism pulls
back to `f^* L ⊗ f^* (dualFLT L) ≅ f^* 𝟙 ≅ 𝟙`, using
`pullbackTensorUnitObjIso f`. Then `inverseUnique` gives the required
isomorphism.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- its uses of `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`, `AlgebraicGeometry.Scheme.Modules.dual` are uses of `IsInvertibleFLT`, `pullbackFLT`, `dualFLT` now;
- applications in dot notation on a hypothesis `h : Scheme.Modules.IsInvertibleFLT L` of lemmas of the name space `Scheme.Modules.IsInvertible` are written out (`h.dual_monoidalV2 …` becomes `Scheme.Modules.IsInvertible.dual_monoidalV2 h …`; `h.pullback f` becomes `Scheme.Modules.IsInvertible.pullbackFLT (hL := h) f`): dot notation looks in the name space `IsInvertibleFLT`, and these lemmas stay in `IsInvertible`; the argument filled is the one dot notation filled;
- the `export` commands that mirror root name spaces inside `P2MW.…` export the renamed names.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
