import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorLineInvariance
import Langlands.AlgebraicGeometry.ProjectiveBundle.TwistTransition
import Langlands.AlgebraicGeometry.LinearSystem.ScalarTwist

/-! # Degree-one transitions after tensoring genuine frames by a line -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.LinearSystem

/-- Multiplication of a coordinate matrix by a unit multiplies each transformed
section by the image of that unit. -/
lemma linearChangeSections_post_smulOfUnit {K : Type u} [CommRing K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
    {L : LineBundle X} {n : ℕ} (s : Fin (n + 1) → GlobalSections L.obj)
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (c : Kˣ) (i : Fin (n + 1)) :
    linearChangeSections p s (e.trans (LinearEquiv.smulOfUnit c)).toLinearMap i =
      Scheme.Modules.scalarsFromBase p (c : K) •
        linearChangeSections p s e.toLinearMap i := by
  change linearChangeSections p s
    ((LinearEquiv.smulOfUnit c).toLinearMap.comp e.toLinearMap) i = _
  rw [← linearChangeSections_comp]
  exact linearChangeSections_smulOfUnit _ _ c i

/-- The scalar formula on covering frames determines a comparison between two
pullback isomorphisms whose scheme maps agree. -/
lemma pullback_comparison_scaled {X Y : Scheme.{u}} {L : Y.Modules}
    (hL : IsLocallyFreeRankOne L) {ι : Type*} (s : ι → GlobalSections L)
    (hs : (⨆ i, trivializationOpen L (s i)) = ⊤)
    (f g : X ⟶ Y) (w : f = g) {N : X.Modules} (c : Γ(X, ⊤)ˣ)
    (α : (Scheme.Modules.pullback f).obj L ≅ N)
    (β : (Scheme.Modules.pullback g).obj L ≅ N)
    (h : ∀ i, α.hom.app ⊤ (pullbackSection f L (s i)) =
      (c : Γ(X, ⊤)) • β.hom.app ⊤ (pullbackSection g L (s i))) :
    α = (Scheme.Modules.pullbackCongr w).app L ≪≫ β ≪≫ Scheme.Modules.unitAut N c := by
  apply Iso.ext
  apply hom_ext_of_generating_sections _ (frameCover_pullback hL s hs f)
  intro i
  change α.hom.app ⊤ (pullbackSection f L (s i)) =
    (Scheme.Modules.unitAut N c).hom.app ⊤
      (β.hom.app ⊤ (((Scheme.Modules.pullbackCongr w).hom.app L).app ⊤
        (pullbackSection f L (s i))))
  rw [pullbackCongr_coordinate, unitAut_hom_app_top]
  exact h i

/-- The transformed relative coordinates retain the scalar coefficient. -/
lemma changedRelativeProjectiveCoordinates_scaled {K : Type u} [CommRing K]
    {S : Scheme.{u}} {n : ℕ} (a : S ⟶ Spec (CommRingCat.of K))
    (e e' : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (c : Kˣ) (he : e' = e.trans (LinearEquiv.smulOfUnit c)) (i : Fin (n + 1)) :
    changedRelativeProjectiveCoordinates a e' i =
      Scheme.Modules.scalarsFromBase (RelativeProjectiveSpace.toBase S n ≫ a) (c : K) •
        changedRelativeProjectiveCoordinates a e i := by
  rw [he]
  exact linearChangeSections_post_smulOfUnit
    (RelativeProjectiveSpace.toBase S n ≫ a)
    (RelativeProjectiveSpace.twistOneCoordinate S n) e c i

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.CoordinateCocycle

open LinearSystem

variable {S : Scheme.{u}} {n : ℕ} {𝒰 : S.OpenCover}
  [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-- A scalar relation between arbitrary coordinate cocycles gives the corresponding
scalar relation between their actual degree-one coordinate formulas. -/
lemma chartTwistIso_coordinate_scaled (d e : CoordinateCocycle n 𝒰)
    {U V : 𝒰.I₀} (h : U ⟶ V) (c : Γ(𝒰.X U, ⊤)ˣ)
    (ht : d.transition h = (e.transition h).trans (LinearEquiv.smulOfUnit c))
    (i : Fin (n + 1)) :
    (d.chartTwistIso h).hom.app ⊤
        (pullbackSection (d.chartFunctor.map h)
          (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj
          (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X V) n i)) =
      Scheme.Modules.scalarsFromBase
        (RelativeProjectiveSpace.toBase (𝒰.X U) n ≫ (𝒰.X U).toSpecΓ) (c : Γ(𝒰.X U, ⊤)) •
        (e.chartTwistIso h).hom.app ⊤
          (pullbackSection (e.chartFunctor.map h)
            (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj
            (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X V) n i)) := by
  exact (d.chartTwistIso_coordinate h i).trans
    ((changedRelativeProjectiveCoordinates_scaled (𝒰.X U).toSpecΓ
      (e.transition h) (d.transition h) c ht i).trans
        (congrArg (fun s => Scheme.Modules.scalarsFromBase
          (RelativeProjectiveSpace.toBase (𝒰.X U) n ≫ (𝒰.X U).toSpecΓ)
          (c : Γ(𝒰.X U, ⊤)) • s) (e.chartTwistIso_coordinate h i).symm))

/-- A scalar coordinate formula determines arbitrary chart comparisons. -/
lemma chartTwist_scaled_criterion (d e : CoordinateCocycle n 𝒰)
    {U V : 𝒰.I₀} (h : U ⟶ V) (c : Γ(𝒰.X U, ⊤)ˣ)
    (ht : d.transition h = (e.transition h).trans (LinearEquiv.smulOfUnit c))
    (w : d.chartFunctor.map h = e.chartFunctor.map h)
    (α : (Scheme.Modules.pullback (d.chartFunctor.map h)).obj
      (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj ≅
      (RelativeProjectiveSpace.twistOne (𝒰.X U) n).obj)
    (β : (Scheme.Modules.pullback (e.chartFunctor.map h)).obj
      (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj ≅
      (RelativeProjectiveSpace.twistOne (𝒰.X U) n).obj)
    (hα : ∀ i, α.hom.app ⊤ (pullbackSection (d.chartFunctor.map h)
      (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X V) n i)) =
        changedRelativeProjectiveCoordinates (𝒰.X U).toSpecΓ (d.transition h) i)
    (hβ : ∀ i, β.hom.app ⊤ (pullbackSection (e.chartFunctor.map h)
      (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj
      (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X V) n i)) =
        changedRelativeProjectiveCoordinates (𝒰.X U).toSpecΓ (e.transition h) i) :
    α = (Scheme.Modules.pullbackCongr w).app
          (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj ≪≫
        β ≪≫ Scheme.Modules.unitAut (RelativeProjectiveSpace.twistOne (𝒰.X U) n).obj
          (Units.map (Scheme.Modules.scalarsFromBase
            (RelativeProjectiveSpace.toBase (𝒰.X U) n ≫ (𝒰.X U).toSpecΓ)).toMonoidHom c) := by
  apply pullback_comparison_scaled
    (X := d.chartFunctor.obj U) (Y := d.chartFunctor.obj V)
    (L := (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj)
    (N := (RelativeProjectiveSpace.twistOne (𝒰.X U) n).obj)
    (RelativeProjectiveSpace.twistOne (𝒰.X V) n).property
    (RelativeProjectiveSpace.twistOneCoordinate (𝒰.X V) n)
    (chartCoordinates_frameCover (𝒰 := 𝒰) V)
  intro i
  exact (hα i).trans
    ((changedRelativeProjectiveCoordinates_scaled (𝒰.X U).toSpecΓ
      (e.transition h) (d.transition h) c ht i).trans
        (congrArg (fun s => Scheme.Modules.scalarsFromBase
          (RelativeProjectiveSpace.toBase (𝒰.X U) n ≫ (𝒰.X U).toSpecΓ)
          (c : Γ(𝒰.X U, ⊤)) • s) (hβ i).symm))

/-- Equality transport and the scalar unit identify the actual degree-one transitions. -/
lemma chartTwistIso_scaled (d e : CoordinateCocycle n 𝒰)
    {U V : 𝒰.I₀} (h : U ⟶ V) (c : Γ(𝒰.X U, ⊤)ˣ)
    (ht : d.transition h = (e.transition h).trans (LinearEquiv.smulOfUnit c))
    (w : d.chartFunctor.map h = e.chartFunctor.map h) :
    d.chartTwistIso h =
      (Scheme.Modules.pullbackCongr w).app
          (RelativeProjectiveSpace.twistOne (𝒰.X V) n).obj ≪≫
        e.chartTwistIso h ≪≫
        Scheme.Modules.unitAut (RelativeProjectiveSpace.twistOne (𝒰.X U) n).obj
          (Units.map (Scheme.Modules.scalarsFromBase
            (RelativeProjectiveSpace.toBase (𝒰.X U) n ≫ (𝒰.X U).toSpecΓ)).toMonoidHom c) := by
  exact d.chartTwist_scaled_criterion e h c ht w
    (d.chartTwistIso h) (e.chartTwistIso h)
    (d.chartTwistIso_coordinate h) (e.chartTwistIso_coordinate h)

end Langlands.AlgebraicGeometry.ProjectiveBundle.CoordinateCocycle

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames

open LinearSystem

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}
variable (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N)

/-- The reversed line-chart unit that multiplies the dual tensor-frame transition. -/
abbrev dualLineTransitionUnit {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    Γ(U.val.toScheme, ⊤)ˣ :=
  Units.map U.val.topIso.inv.hom.toMonoidHom
    (lineComparisonUnit V.property.2.some U.property.2.some U.val (leOfHom h) le_rfl)

/-- The corresponding unit on the actual projective chart. -/
abbrev dualLineProjectiveUnit {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    Γ(RelativeProjectiveSpace U.val.toScheme n, ⊤)ˣ :=
  Units.map (Scheme.Modules.scalarsFromBase
    (RelativeProjectiveSpace.toBase U.val.toScheme n ≫ U.val.toScheme.toSpecΓ)).toMonoidHom
      (dualLineTransitionUnit hM hN h)

/-- The two actual coordinate transitions differ precisely by the reversed line unit. -/
lemma tensor_transition {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (tensorAtlas hM hN).cocycle.transition h =
      ((sourceAtlas hM hN).cocycle.transition h).trans
        (LinearEquiv.smulOfUnit (dualLineTransitionUnit hM hN h)) := by
  change coordinatesOnOpen n U.val
    ((U.property.1.some.tensor U.property.2.some).dual.change
      (V.property.1.some.tensor V.property.2.some).dual U.val le_rfl (leOfHom h)) = _
  rw [LocalFrame.tensor_overlap_dual_change]
  dsimp only [coordinatesOnOpen]
  rw [ProjectiveSpace.coordinateBaseChange_trans,
    ProjectiveSpace.coordinateBaseChange_smulOfUnit]
  rfl

/-- Under the equality of actual projective restriction maps, the tensor twist
transition is the source twist transition followed by the reversed line scalar. -/
lemma tensor_chartTwistIso
    {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (tensorAtlas hM hN).cocycle.chartTwistIso h =
      (Scheme.Modules.pullbackCongr (chartFunctor_map_eq hM hN h)).app
        (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ≪≫
      (sourceAtlas hM hN).cocycle.chartTwistIso h ≪≫
      Scheme.Modules.unitAut (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj
        (dualLineProjectiveUnit hM hN h) := by
  exact (tensorAtlas hM hN).cocycle.chartTwistIso_scaled
    (sourceAtlas hM hN).cocycle h (dualLineTransitionUnit hM hN h)
    (tensor_transition hM hN h) (chartFunctor_map_eq hM hN h)

end Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
