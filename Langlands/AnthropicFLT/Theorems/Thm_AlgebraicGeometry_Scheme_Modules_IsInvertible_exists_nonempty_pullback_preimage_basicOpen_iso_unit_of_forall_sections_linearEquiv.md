# An invertible sheaf with universally free rank-one sections and a trivial fibre is trivial near that fibre

`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv` proves the theorem `AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv`.

## Statement

Let `R` be a noetherian commutative ring in universe `u`, `f : Y ⟶ Spec R` a
proper flat morphism and `P` an invertible sheaf of modules on `Y` (the port's
`Scheme.Modules.IsInvertible`: locally isomorphic to the structure sheaf).
For an `R`-algebra `C`, write `Y_C = Y ×_{Spec R} Spec C` and `P_C` for the
pullback of `P` along the first projection `Y_C ⟶ Y`; global sections are
modules over `R`, respectively `C`, through `f` and the second projection
(`Scheme.TwoAffineOpenCover.moduleSectionsOfHom`). Assume:

- the global sections of `P` are a free `R`-module of rank one, and for every
  `R`-algebra `C` the global sections of `P_C` are a free `C`-module of rank
  one;
- `𝔭` is a prime of `R` with residue field `K`, every nonzero global function
  on the fibre `Y_K` is a unit, and `P_K` is isomorphic to the structure sheaf
  of `Y_K`.

Then there is `g ∈ R` with `g ∉ 𝔭` such that the pullback of `P` to the open
`f⁻¹(D(g))` is isomorphic to its structure sheaf.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv.solution` is written `by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv`, which has the same statement. The Markdown of that module outlines the argument.
