/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import all WeilConjectures.AlgebraicGeometry.AbelianRawPullbackComposition
import all WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

/-! # Composition of raw triangle pullbacks with arbitrary coefficient maps

Source: Stacks Project, Tags 03CB and 09Z1, canonical inverse-image comparisons.
(blueprint: lem-sbc-raw-triangle-pullback-composition).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem rawTriangleMap_comp
    {C B C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C] [Category B] [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    [Preadditive D₀] [Preadditive D₁] [Preadditive D₂]
    [HasShift D₀ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
    (H : C ⥤ B) (H₀ : B ⥤ C₀) (H₁ : B ⥤ C₁) (H₂ : B ⥤ C₂)
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (R : C₀ ⥤ C₂)
    (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂)
    (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) (J : D₀ ⥤ D₂)
    [F.CommShift ℤ] [G.CommShift ℤ] [J.CommShift ℤ]
    (cP : H₁ ≅ H₀ ⋙ P) (cQ : H₂ ≅ H₁ ⋙ Q) (cR : H₂ ≅ H₀ ⋙ R)
    (eP : T₀ ⋙ F ≅ P ⋙ T₁) (eQ : T₁ ⋙ G ≅ Q ⋙ T₂)
    (eR : T₀ ⋙ J ≅ R ⋙ T₂)
    (θ : J ≅ F ⋙ G) [NatTrans.CommShift θ.hom ℤ]
    (U : C) (K : D₀) (L : D₁) (M : D₂)
    (v : F.obj K ⟶ L) (w : G.obj L ⟶ M) (q : ℤ)
    (z : ((H ⋙ H₀ ⋙ T₀).op ⋙ preadditiveYoneda.obj (K⟦q⟧)).obj (op U))
    (hs : T₂.map (cQ.hom.app (H.obj U)) ≫ eQ.inv.app (H₁.obj (H.obj U)) ≫
        G.map (T₁.map (cP.hom.app (H.obj U)) ≫ eP.inv.app (H₀.obj (H.obj U))) =
      T₂.map (cR.hom.app (H.obj U)) ≫ eR.inv.app (H₀.obj (H.obj U)) ≫
        θ.hom.app (T₀.obj (H₀.obj (H.obj U)))) :
    rawTriangleMap (H ⋙ H₀) (H ⋙ H₂) R T₀ T₂ J
        (Functor.whiskerLeft H cR.hom) eR.inv U z
        ((J.commShiftIso q).hom.app K ≫
          (shiftFunctor _ q).map (θ.hom.app K ≫ G.map v ≫ w)) =
      rawTriangleMap (H ⋙ H₁) (H ⋙ H₂) Q T₁ T₂ G
        (Functor.whiskerLeft H cQ.hom) eQ.inv U
        (rawTriangleMap (H ⋙ H₀) (H ⋙ H₁) P T₀ T₁ F
          (Functor.whiskerLeft H cP.hom) eP.inv U z
          ((F.commShiftIso q).hom.app K ≫ (shiftFunctor _ q).map v))
        ((G.commShiftIso q).hom.app L ≫ (shiftFunctor _ q).map w) := by
  change T₀.obj (H₀.obj (H.obj U)) ⟶ K⟦q⟧ at z
  unfold rawTriangleMap
  dsimp only [Functor.whiskerLeft_app, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc] at hs ⊢
  rw [G.commShiftIso_hom_naturality_assoc]
  rw [reassoc_of% hs]
  have hn := θ.hom.naturality z
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hc := NatTrans.shift_app_comm θ.hom q K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj] at hc
  rw [← reassoc_of% hc]

set_option backward.isDefEq.respectTransparency true in
/-- Raw triangle pullbacks compose when their coefficient maps are composed using
 the exact derived inverse-image comparison.

Source: Stacks Project, Tags 03CB and 09Z1; the source and shift factors of
lem-sbc-higher-image-raw-pullback-composition-formula, step 2.
(blueprint: lem-sbc-raw-triangle-pullback-composition).

Proof: Expand both triangle pullbacks as `rawTriangleMap`. Map the inner four
factors through the outer derived pullback, using functoriality. Naturality of
its single-functor comparison moves the inner source morphism to the left.
Composition of the single-functor comparisons identifies the source comparison
for the composite. Associativity of underived pullback composition identifies
its free-sheaf factor. Naturality of the derived composition isomorphism moves
it past the arbitrary class. Naturality of commShiftIso moves the inner
coefficient morphism past the outer shift comparison, and compatibility of the
derived composition isomorphism with shifts identifies the two shift factors.
The remaining shifted coefficient map is the composite displayed here.
This argument uses neither a single-complex presentation of K nor any condition
on the coefficient maps; zero objects, identity maps and negative degrees obey
exactly the same naturality and coherence identities. -/
theorem higherDirectImageRawTrianglePullback_comp
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z S : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (h : Z ⟶ S) (hy : Y ⟶ S) (hx : X ⟶ S)
    (wy : b ≫ h = hy) (wx : a ≫ hy = hx) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((b)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ L)
    (w : D+((a)^*[ModuleCat.{u + 1} Λ]).obj L ⟶ M)
    (U : S.Etale) (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    higherDirectImageRawTrianglePullback Λ (a ≫ b) h hx
        (by rw [Category.assoc, wy, wx]) q K M
        ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a b).hom.app K ≫
          D+((a)^*[ModuleCat.{u + 1} Λ]).map v ≫ w) U z =
      higherDirectImageRawTrianglePullback Λ a hy hx wx q L M w U
        (higherDirectImageRawTrianglePullback Λ b h hy wy q K L v U z) := by
  subst hy
  subst hx
  have : NatTrans.CommShift (upperStarPlusComp (ModuleCat.{u + 1} Λ) a b).hom ℤ := by
    have := Functor.plusNatIso_commShift (upperStarComp (ModuleCat.{u + 1} Λ) a b)
    have := Functor.plusCompIso_commShift (b)^*[ModuleCat.{u + 1} Λ] (a)^*[ModuleCat.{u + 1} Λ]
    dsimp only [upperStarPlusComp, Iso.trans_hom]
    infer_instance
  set_option backward.isDefEq.respectTransparency false in
  exact rawTriangleMap_comp
    (freeSheaf Λ S) (h)^*[ModuleCat.{u + 1} Λ]
    (b ≫ h)^*[ModuleCat.{u + 1} Λ] (a ≫ b ≫ h)^*[ModuleCat.{u + 1} Λ]
    (b)^*[ModuleCat.{u + 1} Λ] (a)^*[ModuleCat.{u + 1} Λ]
    (a ≫ b)^*[ModuleCat.{u + 1} Λ]
    (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    D+((b)^*[ModuleCat.{u + 1} Λ]) D+((a)^*[ModuleCat.{u + 1} Λ])
    D+((a ≫ b)^*[ModuleCat.{u + 1} Λ])
    (upperStarComp (ModuleCat.{u + 1} Λ) b h)
    (upperStarComp (ModuleCat.{u + 1} Λ) a (b ≫ h))
    (upperStarComp (ModuleCat.{u + 1} Λ) (a ≫ b) h (a ≫ b ≫ h)
      (Category.assoc a b h).symm)
    (((b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
    (((a ≫ b)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) a b) U K L M v w q z
    (sourceComp (ModuleCat.{u + 1} Λ) h b a ((freeSheaf Λ S).obj U))

end AlgebraicGeometry.Etale
