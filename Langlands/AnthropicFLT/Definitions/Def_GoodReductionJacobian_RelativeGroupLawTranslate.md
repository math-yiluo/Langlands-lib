# Local isomorphism of sheaves of modules over a base, and translations by a relative group law

Module `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate`, in
namespaces `AlgebraicGeometry.Scheme.Modules` and `GoodReductionJacobian.RelativeGroupLaw`. Schemes and
rings live in a fixed universe `u`.

## Definitions and results

**Isomorphism locally over the base.** Let `q : X ⟶ T` and `M`, `M'` sheaves of modules on `X`.

- `LocallyIsoOver q M M'` means: every point `τ` of `T` has an open neighbourhood `U` such that the
  restrictions of `M` and `M'` to `q⁻¹(U)` (pullbacks along the open immersion `q⁻¹(U) ⟶ X`) are
  isomorphic. So `M ≅ M'` holds locally on the base `T`, not merely locally on `X`.
- `LocallyIsoOver.of_iso`: isomorphic sheaves are locally isomorphic over `T`. `LocallyIsoOver.rfl`,
  `LocallyIsoOver.symm` and `LocallyIsoOver.trans` make it an equivalence relation. Transitivity uses
  `LocallyIsoOver.restrict`, which restricts an isomorphism over `q⁻¹(U)` to `q⁻¹(V)` for `V ⊆ U`.

**Translations.** Let `L : RelativeGroupLaw R f` be a group law on the points of `f : A ⟶ Spec R`, and
`t : T ⟶ Spec R`.

- `L.fstPoint t` and `L.sndPoint t x` are the two `A ×_R T`-points of `A` given by the first projection
  and by `x` composed with the second projection (`fstPoint_coe`, `sndPoint_coe`).
- `L.mulRight t x : A ×_R T ⟶ A` is their product, the translation `(a, τ) ↦ a · x(τ)`. It lies over
  `Spec R` (`mulRight_over`). For `x = 1`, `sndPoint t 1 = 1` (`sndPoint_one`) and `mulRight t 1` is the
  first projection (`mulRight_one`).
- `L.translate x : A ⟶ A`, for an `R`-point `x`, is translation by `x` (`translate_over`;
  `translate_one`: translation by the unit is the identity).
- `L.IsInStabilizer 𝓛 t x`, for a sheaf of modules `𝓛` on `A`, means that the pullbacks of `𝓛` along
  `mulRight t x` and along the first projection `A ×_R T ⟶ A` are locally isomorphic over `T`
  (`LocallyIsoOver` for the second projection). The `T`-point `x` stabilizes the class of `𝓛` in the
  relative Picard functor.
- `isInStabilizer_one`: the unit stabilizes every `𝓛`. `isInStabilizer_unit`: every point stabilizes the
  structure sheaf, since pullbacks of the unit are the unit.

## Provenance and licence

This file is a port of `Definitions/Def_GoodReductionJacobian_RelativeGroupLawTranslate.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_RelativeGroupLaw`,
  `Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel` and
  `Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` are renamed to
  `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
