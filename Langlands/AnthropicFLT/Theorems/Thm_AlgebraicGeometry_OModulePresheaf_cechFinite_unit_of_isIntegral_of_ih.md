# The integral step of the finiteness theorem, via Chow’s lemma and the Leray spectral sequence

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih`.

## Statement

`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`: for a noetherian ring `R`, a proper
`πZ : Z ⟶ Spec R` with `Z` integral, an ordered affine cover `K` of `Z`, and
`ih : ∀ F : OModulePresheaf πZ, F.IsCoherent → F.IsQuasicoherent → ∀ Y' < (⊤ : Closeds Z), F.SupportedIn Y' → F.CechFinite K`,
`(OModulePresheaf.unit πZ).CechFinite K`. As in FLT, the file removes some instances and simp lemmas for the
rest of the file (`attribute [-instance]` and `attribute [-simp]`); this does not affect the statement.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih.solution R _ _ Z πZ _ _ K ih`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The
theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` and the
  corresponding `P2M.Sol` module are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).
