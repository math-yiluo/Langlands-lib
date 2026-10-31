# Finiteness of Čech cohomology of coherent sheaves on a proper scheme over a noetherian ring (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper`. Its only
declaration is `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper.solution`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` proper and `K` an ordered affine cover of `V`.
Every coherent, quasi-coherent presheaf of modules `F` over `π` (`IsCoherent`, `IsQuasicoherent`,
`Def_AlgebraicGeometry_OrderedAffineCoverCech`) has finitely generated Čech cohomology for `K` in every degree
(`F.CechFinite K`). This is the finiteness theorem for the cohomology of coherent sheaves on proper schemes
over a noetherian ring. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper` and proves it from `solution`.

## Proof outline

The proof applies the dévissage principle `OModulePresheaf.cechFinite_of_forall_integral`
(`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral`) with the support `Y = ⊤`.

1. **Integral step.** For a nonempty closed `Z₀` whose reduced subscheme `Z₀S` (the subscheme of the vanishing
   ideal) is integral, assume every coherent quasi-coherent presheaf supported in a smaller closed set has
   finite Čech cohomology. By `OModulePresheaf.cechFinite_pushforward_iff` it suffices to show that the
   structure sheaf of `Z₀S` has finite Čech cohomology for the preimage cover. This is
   `OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih` for the proper morphism `Z₀S ⟶ Spec R`, whose own
   induction hypothesis (presheaves on `Z₀S` supported in proper closed subsets) is supplied by
   `OModulePresheaf.cechFinite_preimage_of_ih` from the hypothesis on `V`.
2. **Support condition.** `F` is supported in `⊤`: on an affine open disjoint from `⊤`, i.e. the empty open,
   the sections are trivial.

As in FLT, the file removes some instances and simp lemmas for the rest of the file (`attribute [-instance]`
and `attribute [-simp]`).

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands.
