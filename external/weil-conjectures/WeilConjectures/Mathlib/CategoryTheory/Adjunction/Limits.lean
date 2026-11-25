/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Left adjoints with invertible counit and comparison maps of colimits

Let `F ⊣ G` be an adjunction whose counit is an isomorphism (i.e. `G` is fully faithful), and
let `Y : J ⥤ D` be a diagram with a colimit cocone `c`. The comparison map
`colim (Y ⋙ G) ⟶ G.obj c.pt` need not be an isomorphism, but `F` sends it to an isomorphism
as soon as `F` preserves the colimit of `Y ⋙ G`.

## Main results

- `Adjunction.isIso_map_colimitDesc_mapCocone`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- If the counit of `F ⊣ G` is an isomorphism and `F` preserves the colimit of `Y ⋙ G`, then
`F` sends the comparison map `colim (Y ⋙ G) ⟶ G.obj c.pt` to an isomorphism. -/
lemma isIso_map_colimitDesc_mapCocone (adj : F ⊣ G) [IsIso adj.counit] {J : Type u₃}
    [Category.{v₃} J] {Y : J ⥤ D} [HasColimit (Y ⋙ G)] [PreservesColimit (Y ⋙ G) F]
    {c : Cocone Y} (hc : IsColimit c) :
    IsIso (F.map (colimit.desc (Y ⋙ G) (G.mapCocone c))) := by
  have hF := isColimitOfPreserves F (colimit.isColimit (Y ⋙ G))
  have hc' := (IsColimit.precomposeHomEquiv
    (asIso (Functor.whiskerLeft Y adj.counit)) c).symm hc
  have : F.map (colimit.desc _ (G.mapCocone c)) ≫ adj.counit.app c.pt =
      (hF.coconePointUniqueUpToIso hc').hom :=
    hF.hom_ext fun j ↦ by
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
      dsimp
      rw [← F.map_comp_assoc, colimit.ι_desc]
      exact adj.counit.naturality (c.ι.app j)
  rw [← isIso_comp_right_iff _ (adj.counit.app c.pt), this]
  infer_instance

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- **Left adjoints preserve colimits.** If `F ⊣ G` and `c` is a colimit cocone of a diagram
`M : J ⥤ C`, then `F.mapCocone c` is a colimit cocone of `M ⋙ F`; this is
`Adjunction.leftAdjoint_preservesColimits`. In particular the canonical morphism
`colimit (M ⋙ F) ⟶ F (colimit M)` is an isomorphism (`preservesColimitIso`).
(blueprint: `situation-conventions`) -/
theorem nonempty_isColimit_mapCocone (adj : F ⊣ G) {J : Type u₃} [Category.{v₃} J]
    {M : J ⥤ C} {c : Cocone M} (hc : IsColimit c) : Nonempty (IsColimit (F.mapCocone c)) := by
  have := adj.leftAdjoint_preservesColimits
  exact ⟨isColimitOfPreserves F hc⟩

/-- **Right adjoints preserve limits.** If `F ⊣ G` and `c` is a limit cone of a diagram
`M : J ⥤ D`, then `G.mapCone c` is a limit cone of `M ⋙ G`
(`Adjunction.rightAdjoint_preservesLimits`). In particular `G` sends a terminal object to a
terminal object, and the comparison morphism `G (Y ⨯ Y') ⟶ G Y ⨯ G Y'` is an isomorphism.
(blueprint: `situation-conventions`) -/
theorem nonempty_isLimit_mapCone (adj : F ⊣ G) {J : Type u₃} [Category.{v₃} J]
    {M : J ⥤ D} {c : Cone M} (hc : IsLimit c) :
    Nonempty (IsLimit (G.mapCone c)) ∧
      (∀ {T : D}, IsTerminal T → Nonempty (IsTerminal (G.obj T))) ∧
      ∀ [HasBinaryProducts C] [HasBinaryProducts D] (Y Y' : D), IsIso (prodComparison G Y Y') := by
  have := adj.rightAdjoint_preservesLimits.{v₃, u₃}
  have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
  refine ⟨⟨isLimitOfPreserves G hc⟩, fun hT ↦ ⟨IsTerminal.isTerminalObj G _ hT⟩, ?_⟩
  intros
  infer_instance


end CategoryTheory.Adjunction
