# Finite Čech cohomology passes to the quotient of a short exact sequence (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` separated, `K` an ordered affine cover of `V`,
and `S : 0 → F₁ → F₂ → F₃ → 0` a short exact sequence of presheaves of modules over `π`, exact on affine
opens. If `F₁` and `F₂` have finitely generated Čech cohomology for `K` (`CechFinite K`), so does `F₃`. The
theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right` and proves it from `solution`.

## Proof outline

Take the connecting maps `δ₀`, `δ` of the FLT theorem `OModulePresheaf.AffSES.exists_connectingHom`. In each
degree the sequence `Ȟⁱ(F₂) → Ȟⁱ(F₃) → Ȟ^{i+1}(F₁)` satisfies `ker ⊆ im` at the middle term, and the outer
terms are finitely generated. The FLT theorem `Module.Finite.of_ker_le_range_of_isNoetherianRing` then makes
`Ȟⁱ(F₃)` finitely generated.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafHom`,
  `Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom` are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands. No
  declaration, statement or proof step changed.
