import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleRestriction
import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Injectives for ordinary direct image from the analytic étale site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe w uC vC uD vD u v uL

namespace Langlands.Sheaf.SiteDirectImage

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D) (R : Type w) [CommRing R]
variable [EssentiallySmall.{w} C] [LocallySmall.{w} D]

local instance hasColimitsCostructuredArrow (T : Dᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow F.op T) (ModuleCat.{w} R) :=
  hasColimitsOfShape_of_essentiallySmall.{w} _ _

local instance hasPointwiseLeftKanExtension (P : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    F.op.HasPointwiseLeftKanExtension P := fun T => by
  have := hasColimitsOfShape_of_essentiallySmall.{w}
    (CostructuredArrow F.op T) (ModuleCat.{w} R)
  infer_instance

/-- The pointwise colimit formula for left Kan extension in independent universes. -/
def lanEvaluationIso (T : Dᵒᵖ) :
    F.op.lan ⋙ (CategoryTheory.evaluation Dᵒᵖ (ModuleCat.{w} R)).obj T ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{w} R)).obj
        (CostructuredArrow.proj F.op T) ⋙ colim :=
  NatIso.ofComponents (fun P =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.op P T)
      (colimit.isColimit _)) (fun {P Q} f => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.op P T).hom_ext
    intro S
    have h₁ := fun (P : Cᵒᵖ ⥤ ModuleCat.{w} R) => IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.op P T)
      (colimit.isColimit _) S
    have h₂ := congr_app (F.op.lanUnit.naturality f) S.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

/-- Flat left Kan extension preserves finite limits for sufficiently small
indexing categories and independent category universes. -/
instance lan_preservesFiniteLimits [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{w} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{w}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    (F.op.lan : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{w} R) J
  intro T
  have : IsFiltered (CostructuredArrow F.op T) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F T.unop)
  have : IsFiltered (SmallModel.{w} (CostructuredArrow F.op T)) :=
    IsFiltered.of_equivalence (equivSmallModel.{w} (CostructuredArrow F.op T))
  have := HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{w} R)
    (equivSmallModel.{w} (CostructuredArrow F.op T)).symm
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIso F R T).symm

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [F.IsContinuous J K] [HasSheafify J (ModuleCat.{w} R)]
  [HasSheafify K (ModuleCat.{w} R)]

/-- The actual inverse image is left Kan extension followed by sheafification. -/
def inverseImage : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf K (ModuleCat.{w} R) :=
  Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{w} R) J K

/-- The sheaf inverse image is left adjoint to literal continuous direct image. -/
def adjunction : inverseImage F R J K ⊣ F.sheafPushforwardContinuous (ModuleCat.{w} R) J K :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (ModuleCat.{w} R) J K

instance inverseImage_preservesFiniteLimits [RepresentablyFlat F] :
    PreservesFiniteLimits (inverseImage F R J K) := by
  dsimp only [inverseImage, Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

omit [HasSheafify J (ModuleCat.{w} R)] in
/-- Direct image for a flat continuous functor preserves injective module sheaves. -/
theorem preservesInjectiveObjects [RepresentablyFlat F] :
    (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction F R J K)

end Langlands.Sheaf.SiteDirectImage

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

private theorem ordinaryOpens_essentiallySmall :
    EssentiallySmall.{max u (v + 1) uL} (Opens (localizedSpaceFunctor.obj X)) := by
  have : Small.{max u (v + 1) uL} (Opens (localizedSpaceFunctor.obj X)) :=
    small_lift.{v, max u (v + 1) uL, v} _
  exact essentiallySmall_of_small_of_locallySmall _

/-- Module sheaves on the actual ordinary-open site have sheafification. -/
theorem underlyingTopology_hasSheafify :
    HasSheafify (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
      (ModuleCat.{max u (v + 1) uL} R) := by
  have := ordinaryOpens_essentiallySmall.{u, v, uL} X
  exact hasSheafifyEssentiallySmallSite
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (ModuleCat.{max u (v + 1) uL} R)

/-- The inverse image left adjoint of actual ordinary direct image. -/
def etaleUnderlyingInverseImage :
    TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X) ⥤
      Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) := by
  have := ordinaryOpens_essentiallySmall.{u, v, uL} X
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := etale_hasSheafify.{u, v, uL} X R
  exact Langlands.Sheaf.SiteDirectImage.inverseImage (openEtaleFunctor X) R
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (etaleTopology X)

/-- The actual inverse and direct images form the ordinary/étale site adjunction. -/
def etaleUnderlyingAdjunction :
    etaleUnderlyingInverseImage.{u, v, uL} X R ⊣
      etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R) := by
  have := ordinaryOpens_essentiallySmall.{u, v, uL} X
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := etale_hasSheafify.{u, v, uL} X R
  exact Langlands.Sheaf.SiteDirectImage.adjunction (openEtaleFunctor X) R
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (etaleTopology X)

instance etaleUnderlyingInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (etaleUnderlyingInverseImage.{u, v, uL} X R) := by
  have := ordinaryOpens_essentiallySmall.{u, v, uL} X
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := etale_hasSheafify.{u, v, uL} X R
  exact Langlands.Sheaf.SiteDirectImage.inverseImage_preservesFiniteLimits (openEtaleFunctor X) R
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)) (etaleTopology X)

/-- Ordinary direct image preserves injectives; this is distinct from the
restriction of equivariant or locally discrete sheaves. -/
instance etaleUnderlyingSheaf_preservesInjectiveObjects :
    (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).PreservesInjectiveObjects := by
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := etale_hasSheafify.{u, v, uL} X R
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (etaleUnderlyingAdjunction.{u, v, uL} X R)

end Langlands.Sheaf.Equivariant.Analytic
