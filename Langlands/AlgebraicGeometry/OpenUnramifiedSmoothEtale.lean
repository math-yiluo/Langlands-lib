import Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement
import Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes
import Langlands.AlgebraicGeometry.SmoothDomainStalksProof
import Langlands.AlgebraicGeometry.SmoothIntegralNormalStalksProof
import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralProof

/-! # Component reduction for open unramified maps of smooth schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry

/-- Actual open connected components of smooth field schemes are integral. -/
theorem componentScheme_isIntegral_of_smooth
    {K : Type u} [Field K] (X : Scheme.{u}) [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [Smooth p]
    (c : _root_.ConnectedComponents X) : IsIntegral (componentScheme X c) := by
  have : Smooth (componentι X c ≫ p) := inferInstance
  exact connectedLocallyNoetherianDomainStalksIntegral (componentScheme X c)
    inferInstance inferInstance
    (smoothDomainStalks K _ (componentι X c ≫ p) inferInstance)

/-- An open morphism restricts to an open map between its actual source
component and the image component. -/
theorem componentHom_isOpenMap {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : IsOpenMap f) (c : _root_.ConnectedComponents X) :
    IsOpenMap (componentHom f c) := by
  have hcomp : IsOpenMap
      (componentHom f c ≫ componentι Y (componentMap f c)) := by
    rw [componentHom_ι]
    exact hf.comp (componentι X c).isOpenEmbedding.isOpenMap
  exact ((componentι Y (componentMap f c)).isOpenEmbedding.isOpenMap_iff).mpr hcomp

/-- Conditional component reduction using the precise missing generic
dominant-unramified criterion. This does not prove that criterion. -/
theorem openUnramifiedSmooth_etale_of_dominantCriterion
    (criterion : DominantUnramifiedEtaleStatement.{u})
    {K : Type u} [Field K]
    (X Y : Scheme.{u}) (pX : X ⟶ Spec (CommRingCat.of K))
    (pY : Y ⟶ Spec (CommRingCat.of K))
    [Smooth pX] [Smooth pY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [FormallyUnramified f] (hf : IsOpenMap f) :
    Etale f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (componentOpenCover X)]
  intro c
  let d := componentMap f c
  have : IsIntegral (componentScheme X c) :=
    componentScheme_isIntegral_of_smooth X pX c
  have : IsIntegral (componentScheme Y d) :=
    componentScheme_isIntegral_of_smooth Y pY d
  have hY : GeometricallyUnibranchIntegralScheme (componentScheme Y d) := by
    apply geometricallyUnibranchIntegralScheme_of_stalks
    intro y
    have : Smooth (componentι Y d ≫ pY) := inferInstance
    exact smoothIntegralNormalStalks K _ (componentι Y d ≫ pY) inferInstance y
  have : LocallyOfFiniteType (componentHom f c ≫ componentι Y d) := by
    rw [componentHom_ι]
    infer_instance
  have : LocallyOfFiniteType (componentHom f c) :=
    locallyOfFiniteType_of_comp (componentHom f c) (componentι Y d)
  have : FormallyUnramified (componentHom f c ≫ componentι Y d) := by
    rw [componentHom_ι]
    exact MorphismProperty.comp_mem (@FormallyUnramified)
      (componentι X c) f inferInstance inferInstance
  have : FormallyUnramified (componentHom f c) :=
    FormallyUnramified.of_comp (componentHom f c) (componentι Y d)
  have : IsDominant (componentHom f c) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      (componentHom_isOpenMap f hf c)⟩
  have : Etale (componentHom f c) :=
    criterion (componentScheme X c) (componentScheme Y d) (componentHom f c)
      hY inferInstance inferInstance inferInstance
  change Etale (componentι X c ≫ f)
  rw [← componentHom_ι f c]
  infer_instance

end Langlands.AlgebraicGeometry
