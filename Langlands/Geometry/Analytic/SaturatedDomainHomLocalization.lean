import Langlands.Geometry.Analytic.SaturatedDomainHomPresheaf
import Langlands.Geometry.Analytic.OriginalDomainNested

/-! # Quotient morphisms under localization of actual domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

open CategoryTheory Set
open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Insert the intermediate subspace in a domain object. The quotient arrow
is constructed by the proved image-only domain universal property. -/
def domainNestedMap (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    ofPresentation (A.originalDomain (S.subspaceExtend U)) ⟶
      ofPresentation ((A.originalDomain S).originalDomain U) :=
  domainLift U (domainMap (S.subspaceExtend_le U)) (by
    intro x
    apply (S.mem_subspaceExtend_iff U _).mp
    erw [domainMap_apply_val]
    exact x.property)

@[simp]
theorem domainNestedMap_inclusion (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    domainNestedMap S U ≫ domainInclusion (A.originalDomain S) U =
      domainMap (S.subspaceExtend_le U) :=
  domainLift_comp_inclusion U _ _

/-- Forget the intermediate subspace in a domain object, using the actual
double inclusion and its literal image in the ambient extended domain. -/
def domainNestedInverse (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    ofPresentation ((A.originalDomain S).originalDomain U) ⟶
      ofPresentation (A.originalDomain (S.subspaceExtend U)) :=
  domainLift (S.subspaceExtend U)
    (domainInclusion (A.originalDomain S) U ≫ domainInclusion A S) (by
    intro x
    erw [Functor.map_comp]
    change spaceFunctor.map (domainInclusion A S)
      (spaceFunctor.map (domainInclusion (A.originalDomain S) U) x) ∈
        S.subspaceExtend U
    erw [domainInclusion_apply, domainInclusion_apply]
    exact ⟨x.val, x.property, rfl⟩)

@[simp]
theorem domainNestedInverse_ambientInclusion
    (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    domainNestedInverse S U ≫ domainInclusion A (S.subspaceExtend U) =
      domainInclusion (A.originalDomain S) U ≫ domainInclusion A S :=
  domainLift_comp_inclusion (S.subspaceExtend U) _ _

@[simp]
theorem domainNestedInverse_map (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    domainNestedInverse S U ≫ domainMap (S.subspaceExtend_le U) =
      domainInclusion (A.originalDomain S) U := by
  apply (cancel_mono (domainInclusion A S)).1
  erw [Category.assoc, domainMap_inclusion, domainNestedInverse_ambientInclusion]

set_option maxHeartbeats 800000 in
/-- Ambient realization of a subspace domain and its nested realization are
isomorphic in the actual quotient category, including all bounded map data. -/
def domainNestedIso (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    ofPresentation (A.originalDomain (S.subspaceExtend U)) ≅
      ofPresentation ((A.originalDomain S).originalDomain U) where
  hom := domainNestedMap S U
  inv := domainNestedInverse S U
  hom_inv_id := by
    apply (cancel_mono (domainInclusion A (S.subspaceExtend U))).1
    erw [Category.assoc, domainNestedInverse_ambientInclusion, ← Category.assoc,
      domainNestedMap_inclusion, domainMap_inclusion, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (domainInclusion (A.originalDomain S) U)).1
    erw [Category.assoc, domainNestedMap_inclusion, domainNestedInverse_map,
      Category.id_comp]

@[simp]
theorem domainNestedMap_apply (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain)
    (x : (S.subspaceExtend U).carrier) :
    (spaceFunctor.map (domainNestedMap S U) x).val.val = x.val := by
  change (spaceFunctor.map (domainLift U (domainMap _) _) x).val.val = x.val
  erw [domainLift_apply, domainMap_apply_val]

@[simp]
theorem domainNestedInverse_apply (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain)
    (x : U.carrier) :
    (spaceFunctor.map (domainNestedInverse S U) x).val = x.val.val := by
  unfold domainNestedInverse
  erw [domainLift_apply, Functor.map_comp]
  change spaceFunctor.map (domainInclusion A S)
    (spaceFunctor.map (domainInclusion (A.originalDomain S) U) x) = x.val.val
  erw [domainInclusion_apply, domainInclusion_apply]

/-- Inserting intermediate membership commutes with every domain inclusion
as an equality of complete quotient arrows. -/
theorem domainNestedMap_naturality (S : A.presentation.atlas.OriginalChartDomain)
    {U V : (A.originalDomain S).presentation.atlas.OriginalChartDomain}
    (hUV : U ≤ V) :
    domainMap (S.subspaceExtend_mono hUV) ≫ domainNestedMap S V =
      domainNestedMap S U ≫ domainMap hUV := by
  apply (cancel_mono (domainInclusion (A.originalDomain S) V)).1
  erw [Category.assoc, domainNestedMap_inclusion, domainMap_comp,
    Category.assoc, domainMap_inclusion, domainNestedMap_inclusion]

/-- Realization in the quotient commutes naturally with localization of the
actual original-chart domain category to a subspace. -/
def domainNestedNatIso (S : A.presentation.atlas.OriginalChartDomain) :
    S.subspaceExtensionFunctor ⋙ domainFunctor A ≅
      domainFunctor (A.originalDomain S) :=
  NatIso.ofComponents (domainNestedIso S)
    (fun f => domainNestedMap_naturality S (leOfHom f))

/-- Quotient morphisms on the two actual presentations of a nested domain
correspond by precomposing with the constructed inverse comparison. -/
def domainHomNestedEquiv (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain) :
    (ofPresentation (A.originalDomain (S.subspaceExtend U)) ⟶ ofPresentation B) ≃
      (ofPresentation ((A.originalDomain S).originalDomain U) ⟶ ofPresentation B) where
  toFun F := domainNestedInverse S U ≫ F
  invFun G := domainNestedMap S U ≫ G
  left_inv F := by
    change domainNestedMap S U ≫ (domainNestedInverse S U ≫ F) = F
    erw [← Category.assoc, (domainNestedIso S U).hom_inv_id, Category.id_comp]
  right_inv G := by
    change domainNestedInverse S U ≫ (domainNestedMap S U ≫ G) = G
    erw [← Category.assoc, (domainNestedIso S U).inv_hom_id, Category.id_comp]

/-- Forgetting intermediate membership also commutes with every inclusion. -/
theorem domainNestedInverse_naturality (S : A.presentation.atlas.OriginalChartDomain)
    {U V : (A.originalDomain S).presentation.atlas.OriginalChartDomain}
    (hUV : U ≤ V) :
    domainMap hUV ≫ domainNestedInverse S V =
      domainNestedInverse S U ≫ domainMap (S.subspaceExtend_mono hUV) := by
  apply (cancel_mono (domainInclusion A (S.subspaceExtend V))).1
  erw [Category.assoc, domainNestedInverse_ambientInclusion, ← Category.assoc,
    domainMap_inclusion, Category.assoc, domainMap_inclusion,
    domainNestedInverse_ambientInclusion]

/-- The actual quotient-Hom presheaf on a domain is naturally the ambient
quotient-Hom presheaf pulled back along domain extension. -/
def domainHomLocalization (A B : SaturatedAtlasPresentation.{u, v, w} K)
    (S : A.presentation.atlas.OriginalChartDomain) :
    S.subspaceExtensionFunctor.op ⋙ domainHomPresheaf A B ≅
      domainHomPresheaf (A.originalDomain S) B :=
  NatIso.ofComponents (fun U => (domainHomNestedEquiv (B := B) S U.unop).toIso)
    (fun h => by
      apply ConcreteCategory.hom_ext
      intro F
      change domainNestedInverse S _ ≫
          (domainMap (S.subspaceExtend_mono (leOfHom h.unop)) ≫ F) =
        domainMap (leOfHom h.unop) ≫ (domainNestedInverse S _ ≫ F)
      erw [← Category.assoc, ← Category.assoc, domainNestedInverse_naturality])

@[simp]
theorem domainHomLocalization_hom_app
    (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain)
    (F : ofPresentation (A.originalDomain (S.subspaceExtend U)) ⟶ ofPresentation B) :
    (domainHomLocalization A B S).hom.app (Opposite.op U) F =
      domainNestedInverse S U ≫ F := rfl

/-- Localization commutes with arbitrary quotient-valued target maps. -/
theorem domainHomLocalization_postcomp
    {C : SaturatedAtlasPresentation.{u, v, w} K}
    (S : A.presentation.atlas.OriginalChartDomain)
    (U : (A.originalDomain S).presentation.atlas.OriginalChartDomain)
    (F : ofPresentation (A.originalDomain (S.subspaceExtend U)) ⟶ ofPresentation B)
    (G : ofPresentation B ⟶ ofPresentation C) :
    (domainHomLocalization A C S).hom.app (Opposite.op U) (F ≫ G) =
      (domainHomLocalization A B S).hom.app (Opposite.op U) F ≫ G := by
  change domainNestedInverse S U ≫ (F ≫ G) = (domainNestedInverse S U ≫ F) ≫ G
  exact (Category.assoc _ _ _).symm

end Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory
