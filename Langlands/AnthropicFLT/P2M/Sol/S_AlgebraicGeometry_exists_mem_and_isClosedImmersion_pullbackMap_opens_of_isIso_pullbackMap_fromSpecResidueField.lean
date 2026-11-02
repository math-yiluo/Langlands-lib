/-
Ported from `P2M/Sol/S_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz
namespace P2MW.S_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{uz}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsClosedImmersion (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
  obtain ⟨hfib, V₀, hy₀, hfin⟩ :=
    AlgebraicGeometry.isIso_fiberToSpecResidueField_and_exists_isFinite_morphismRestrict_of_isIso_pullbackMap_fromSpecResidueField p q h w y hy
  exact AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField p q h w y V₀ hy₀ hfin hfib
