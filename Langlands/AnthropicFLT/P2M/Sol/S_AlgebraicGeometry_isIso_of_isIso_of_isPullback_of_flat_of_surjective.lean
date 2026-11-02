/-
Ported from `P2M/Sol/S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
namespace P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S S' A B A' B' : Scheme.{uz}} (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (pA : A ⟶ S) (pB : B ⟶ S) (φ : A ⟶ B) (hφ : φ ≫ pB = pA)
    (pA' : A' ⟶ S') (pB' : B' ⟶ S') (φ' : A' ⟶ B') (hφ' : φ' ≫ pB' = pA')
    (gA : A' ⟶ A) (gB : B' ⟶ B) (sqA : IsPullback gA pA' pA b) (sqB : IsPullback gB pB' pB b)
    (comm : φ' ≫ gB = gA ≫ φ) (hiso : IsIso φ') :
    IsIso φ := by

  have outer : IsPullback (φ' ≫ pB') gA b (φ ≫ pB) := by
    rw [hφ', hφ]
    exact sqA.flip
  have sq : IsPullback φ' gA gB φ := IsPullback.of_right outer comm sqB.flip

  have hS : Surjective gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hF : Flat gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hQ : QuasiCompact gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{uz}) gB := ⟨⟨hS, hF⟩, hQ⟩
  have hP : (MorphismProperty.isomorphisms Scheme.{uz}) φ' := (MorphismProperty.isomorphisms.iff _).mpr hiso
  exact (MorphismProperty.isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{uz})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq hQ' hP)
