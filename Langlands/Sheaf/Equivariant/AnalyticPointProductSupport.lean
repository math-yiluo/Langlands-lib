import Langlands.Sheaf.PointProductSupport
import Langlands.Sheaf.Equivariant.AnalyticEtaleSupport
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof

/-! # Compact support lifting for analytic point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointProduct

universe u v uL wI w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)

/-- The identity étale object is terminal in the analytic étale site. -/
def etaleSelfIsTerminal : IsTerminal (etaleSelf X) :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id _))
    (fun U f => MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))

/-- The inverse image of a closed underlying-point set has separating
complementary étale neighborhoods. -/
theorem separatesComplement_etalePoints_preimage
    (hlift : EtalePointLifting L (X := X))
    (C : Set (localizedSpaceFunctor.obj X)) (hC : IsClosed C) :
    SeparatesComplement.{_, max u (v + 1) uL} (etalePoints L h) (etaleSelf X)
      (pointProjection L X ⁻¹' C) := by
  have := etaleSite_locallySmall_points.{u, v, uL} X
  intro i x hi
  let D := (presentationOf X).openDomain Cᶜ hC.isOpen_compl
  let Y : EtaleSite X := MorphismProperty.Over.mk ⊤ (domainι X D)
    (etaleOpenDomainStatement X Cᶜ hC.isOpen_compl)
  let f : Y ⟶ etaleSelf X :=
    MorphismProperty.Over.homMk Y.hom (Category.comp_id _)
  have hiY : pointProjection L X i ∈ Set.range (localizedSpaceFunctor.map Y.hom) := by
    refine ⟨⟨pointProjection L X i, hi⟩, ?_⟩
    exact domainι_apply D _
  obtain ⟨y⟩ := hlift i Y hiY
  refine ⟨Y, f, ULift.up y, ?_, ?_⟩
  · let := (etalePoints L h i).uniqueFiberObj (etaleSelf X) etaleSelfIsTerminal
    exact Subsingleton.elim _ _
  · rintro j ⟨z⟩
    have hj : pointProjection L X j =
        localizedSpaceFunctor.map Y.hom (pointProjection L Y.left z.down.1) :=
      (congrArg (pointProjection L X) z.down.2).symm.trans
        (pointProjection_map L Y.hom z.down.1)
    change pointProjection L X j ∉ C
    rw [hj]
    change localizedSpaceFunctor.map (domainι X D) _ ∉ C
    rw [domainι_apply]
    exact (pointProjection L Y.left z.down.1).property

/-- Compact sets of analytic field-valued points have compact separating
enlargements on a Hausdorff underlying space. -/
theorem hasCompactSeparatingBounds_etalePoints
    [T2Space (localizedSpaceFunctor.obj X)] :
    letI := pointTopology L X
    HasCompactSeparatingBounds.{_, max u (v + 1) uL} (etalePoints L h) (etaleSelf X) := by
  let := pointTopology L X
  intro C hC
  let D := pointProjection L X '' C
  have hD : IsCompact D :=
    hC.image (isInducing_pointProjection L X).continuous
  refine ⟨pointProjection L X ⁻¹' D,
    (isInducing_pointProjection L X).isCompact_preimage' hD
      (Set.image_subset_range _ _),
    Set.subset_preimage_image _ _, ?_⟩
  exact separatesComplement_etalePoints_preimage L h
    (etalePointLifting_of_openDomains L h (etaleOpenDomainStatement X)) D hD.isClosed

variable {R : Type (max u (v + 1) uL)} [CommRing R]

private local instance {S : Type w} [CommRing S] :
    HasProducts.{wI} (ModuleCat.{max wI w} S) := by
  let := hasLimitsOfSizeShrink.{wI, wI, w, w} (ModuleCat.{max wI w} S)
  infer_instance

/-- Actual compact sections of analytic point products lift along every
coefficientwise surjection. -/
theorem etaleCompactSections_pointProduct_map_surjective
    [T2Space (localizedSpaceFunctor.obj X)]
    {M N : (localizedFieldPointFunctor L).obj X → ModuleCat.{max u (v + 1) uL} R}
    (f : M ⟶ N) (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective
      ((etaleCompactSections L h R).map
        ((productFunctor (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R)).map f)) := by
  let := pointTopology L X
  have := etaleSite_locallySmall_points.{u, v, uL} X
  exact compactSections_map_surjective.{_, max u (v + 1) uL} (etalePoints L h) M
    (etaleSelf X) etaleSelfIsTerminal
    (hasCompactSeparatingBounds_etalePoints L h) f hf

end Langlands.Sheaf.Equivariant.Analytic
