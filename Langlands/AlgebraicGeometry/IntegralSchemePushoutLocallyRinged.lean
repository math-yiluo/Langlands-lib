import Langlands.AlgebraicGeometry.IntegralSchemePushoutGluing
import Langlands.AlgebraicGeometry.IntegralSchemePushoutOpenCharts

/-! # Open comparisons of locally ringed colimits -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology AlgebraicGeometry

universe u v w

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PresheafedColimit

variable {J : Type v} [Category.{w} J]
variable {C : Type (u + 1)} [Category.{u} C]
variable [HasColimitsOfShape J TopCat.{u}] [HasLimitsOfShape Jᵒᵖ C]
variable {F G : J ⥤ PresheafedSpace.{u, u + 1, u} C} (τ : F ⟶ G)

/-- The canonical colimit identifies with any supplied colimit cocone point. -/
def comparisonIso {c : Cocone F} (hc : IsColimit c) : colimit F ≅ c.pt :=
  (colimit.isColimit F).coconePointUniqueUpToIso hc

/-- Cartesian open subdiagrams induce open immersions of presheafed colimits. -/
lemma isOpenImmersion_colimMap_of_cartesian
    [hτ : ∀ j, PresheafedSpace.IsOpenImmersion (τ.app j)]
    (hcart : ∀ {j k} (f : j ⟶ k),
      (G.map f).base ⁻¹' Set.range (τ.app k).base = Set.range (τ.app j).base) :
    PresheafedSpace.IsOpenImmersion (colim.map τ) := by
  obtain ⟨hopen, hrange⟩ := TopologicalColimit.isOpenEmbedding_of_cartesian
    (Functor.whiskerRight τ (PresheafedSpace.forget C))
    (isColimitOfPreserves (PresheafedSpace.forget C) (colimit.isColimit F))
    (isColimitOfPreserves (PresheafedSpace.forget C) (colimit.isColimit G))
    (colim.map τ).base
    (fun j => (PresheafedSpace.forget C).congr_map (colimit.ι_map τ j))
    (fun j => (hτ j).base_open) hcart
  exact isOpenImmersion_colimMap τ hopen hrange

/-- The open-immersion criterion is independent of the choice of colimit cocones. -/
lemma isOpenImmersion_of_cartesian {cF : Cocone F} {cG : Cocone G}
    (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j, cF.ι.app j ≫ q = τ.app j ≫ cG.ι.app j)
    [hτ : ∀ j, PresheafedSpace.IsOpenImmersion (τ.app j)]
    (hcart : ∀ {j k} (f : j ⟶ k),
      (G.map f).base ⁻¹' Set.range (τ.app k).base = Set.range (τ.app j).base) :
    PresheafedSpace.IsOpenImmersion q := by
  have := isOpenImmersion_colimMap_of_cartesian τ hcart
  let eF := comparisonIso hcF
  let eG := comparisonIso hcG
  have he : eF.hom ≫ q = colim.map τ ≫ eG.hom := by
    apply colimit.hom_ext
    intro j
    have heF : colimit.ι F j ≫ eF.hom = cF.ι.app j :=
      (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hcF j
    have heG : colimit.ι G j ≫ eG.hom = cG.ι.app j :=
      (colimit.isColimit G).comp_coconePointUniqueUpToIso_hom hcG j
    rw [← Category.assoc, heF, colimit.ι_map_assoc, heG]
    exact hq j
  have heq : q = eF.inv ≫ colim.map τ ≫ eG.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

end PresheafedColimit

namespace LocallyRingedColimit

/-- The forgetful functor used to compute the relevant section maps. -/
abbrev forgetToPresheafedSpace : LocallyRingedSpace.{u} ⥤
    PresheafedSpace CommRingCat.{u} :=
  LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

variable {J : Type v} [Category.{w} J]
variable [HasColimitsOfShape J TopCat.{u}] [HasLimitsOfShape Jᵒᵖ CommRingCat.{u}]
variable {F G : J ⥤ LocallyRingedSpace.{u}} (τ : F ⟶ G)
variable [PreservesColimit F forgetToPresheafedSpace]
variable [PreservesColimit G forgetToPresheafedSpace]

/-- Compatible open subdiagrams induce open immersions of locally ringed colimits. -/
lemma isOpenImmersion_of_cartesian {cF : Cocone F} {cG : Cocone G}
    (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j, cF.ι.app j ≫ q = τ.app j ≫ cG.ι.app j)
    [hτ : ∀ j, LocallyRingedSpace.IsOpenImmersion (τ.app j)]
    (hcart : ∀ {j k} (f : j ⟶ k),
      (G.map f).base ⁻¹' Set.range (τ.app k).base = Set.range (τ.app j).base) :
    LocallyRingedSpace.IsOpenImmersion q := by
  have : ∀ j, PresheafedSpace.IsOpenImmersion
      ((Functor.whiskerRight τ forgetToPresheafedSpace).app j) := fun j => hτ j
  exact PresheafedColimit.isOpenImmersion_of_cartesian
    (Functor.whiskerRight τ forgetToPresheafedSpace)
    (isColimitOfPreserves forgetToPresheafedSpace hcF)
    (isColimitOfPreserves forgetToPresheafedSpace hcG)
    (forgetToPresheafedSpace.map q)
    (fun j => forgetToPresheafedSpace.congr_map (hq j)) hcart

/-- The induced chart has exactly the prescribed inverse images on every component. -/
lemma range_of_cartesian {cF : Cocone F} {cG : Cocone G}
    (hcF : IsColimit cF) (hcG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt)
    (hq : ∀ j, cF.ι.app j ≫ q = τ.app j ≫ cG.ι.app j)
    [hτ : ∀ j, LocallyRingedSpace.IsOpenImmersion (τ.app j)]
    (hcart : ∀ {j k} (f : j ⟶ k),
      (G.map f).base ⁻¹' Set.range (τ.app k).base = Set.range (τ.app j).base) :
    ∀ j, Set.range (τ.app j).base =
      (cG.ι.app j).base ⁻¹' Set.range q.base := by
  exact (TopologicalColimit.isOpenEmbedding_of_cartesian
    (Functor.whiskerRight (Functor.whiskerRight τ forgetToPresheafedSpace)
      (PresheafedSpace.forget CommRingCat))
    (isColimitOfPreserves (PresheafedSpace.forget CommRingCat)
      (isColimitOfPreserves forgetToPresheafedSpace hcF))
    (isColimitOfPreserves (PresheafedSpace.forget CommRingCat)
      (isColimitOfPreserves forgetToPresheafedSpace hcG))
    q.base
    (fun j => (PresheafedSpace.forget CommRingCat).congr_map
      (forgetToPresheafedSpace.congr_map (hq j)))
    (fun j => (hτ j).base_open) hcart).2

end LocallyRingedColimit

end Langlands.AlgebraicGeometry.IntegralSchemePushout
