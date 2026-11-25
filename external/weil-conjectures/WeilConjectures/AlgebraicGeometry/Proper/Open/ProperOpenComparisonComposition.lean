/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenIdentificationNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

/-!
# Composition and identity of proper-open comparison maps

## References

* Stacks Project, Tag 0D6E
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Naturality and the right triangle turn conjugate unit equations into counit equations.
private theorem counit_of_unit
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : L₂ ⟶ L₁) (c : R₁ ⟶ R₂)
    (h : ∀ N, adj₁.unit.app N ≫ c.app (L₁.obj N) =
      adj₂.unit.app N ≫ R₂.map (e.app N)) (M : D) :
    L₂.map (c.app M) ≫ adj₂.counit.app M =
      e.app (R₁.obj M) ≫ adj₁.counit.app M := by
  apply (adj₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit, Adjunction.right_triangle_components,
    Category.comp_id, Functor.map_comp, ← Category.assoc]
  rw [← h, Category.assoc, ← c.naturality]
  simp only [← Category.assoc, Adjunction.right_triangle_components, Category.id_comp,
    Functor.id_obj]

-- The canonical restriction map, expressed entirely through the derived counit.
private noncomputable def restriction
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : D ⥤ E} {R : E ⥤ D} (adj : F ⊣ R)
    (U : E ⥤ C) (V : D ⥤ C) (k : V ≅ F ⋙ U) :
    R ⋙ V ⟶ U where
  app M := k.hom.app (R.obj M) ≫ U.map (adj.counit.app M)
  naturality {M N} b := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [reassoc_of% k.hom.naturality (R.map b)]
    rw [← U.map_comp, adj.counit_naturality, U.map_comp]
    exact (Category.assoc _ _ _).symm

-- Associativity of pullback and the conjugate counit equation give composition of restriction.
private theorem restriction_comp
    {C D₁ D₂ D₃ : Type*} [Category* C] [Category* D₁] [Category* D₂] [Category* D₃]
    {F : D₂ ⥤ D₁} {G : D₃ ⥤ D₂} {H : D₃ ⥤ D₁}
    {R : D₁ ⥤ D₂} {S : D₂ ⥤ D₃} {Q : D₁ ⥤ D₃}
    (adjF : F ⊣ R) (adjG : G ⊣ S) (adjH : H ⊣ Q)
    (U₁ : D₁ ⥤ C) (U₂ : D₂ ⥤ C) (U₃ : D₃ ⥤ C)
    (kf : U₂ ≅ F ⋙ U₁) (kg : U₃ ≅ G ⋙ U₂) (kh : U₃ ≅ H ⋙ U₁)
    (e : H ≅ G ⋙ F) (c : R ⋙ S ≅ Q)
    (ha : ∀ N, kh.hom.app N ≫ U₁.map (e.hom.app N) =
      kg.hom.app N ≫ kf.hom.app (G.obj N))
    (hc : ∀ M, H.map (c.hom.app M) ≫ adjH.counit.app M =
      e.hom.app ((R ⋙ S).obj M) ≫
        F.map (adjG.counit.app (R.obj M)) ≫ adjF.counit.app M)
    (M : D₁) :
    U₃.map (c.hom.app M) ≫ (restriction adjH U₁ U₃ kh).app M =
      (restriction adjG U₂ U₃ kg).app (R.obj M) ≫
        (restriction adjF U₁ U₂ kf).app M := by
  dsimp only [Functor.comp_obj] at hc ⊢
  dsimp only [restriction]
  rw [reassoc_of% kh.hom.naturality (c.hom.app M)]
  rw [← U₁.map_comp, hc, Functor.map_comp, Functor.map_comp, ← Category.assoc, ha]
  rw [Category.assoc, ← reassoc_of% kf.hom.naturality (adjG.counit.app (R.obj M))]
  simp only [Category.assoc]

-- The adjunction calculation applies to any natural restriction maps with these normalizations.
private theorem comparison_comp
    {C D₁ D₂ D₃ : Type*} [Category* C] [Category* D₁] [Category* D₂] [Category* D₃]
    {J₁ : C ⥤ D₁} {J₂ : C ⥤ D₂} {J₃ : C ⥤ D₃}
    {U₁ : D₁ ⥤ C} {U₂ : D₂ ⥤ C} {U₃ : D₃ ⥤ C}
    (a₁ : J₁ ⊣ U₁) (a₂ : J₂ ⊣ U₂) (a₃ : J₃ ⊣ U₃)
    (R : D₁ ⥤ D₂) (S : D₂ ⥤ D₃) (Q : D₁ ⥤ D₃) (c : R ⋙ S ≅ Q)
    (tf : R ⋙ U₂ ⟶ U₁) (tg : S ⋙ U₃ ⟶ U₂) (th : Q ⋙ U₃ ⟶ U₁)
    (ht : ∀ M, U₃.map (c.hom.app M) ≫ th.app M = tg.app (R.obj M) ≫ tf.app M)
    (K : C) [Mono (a₁.unit.app K)]
    (θf : U₂.obj (R.obj (J₁.obj K)) ≅ K)
    (θg : U₃.obj (S.obj (J₂.obj K)) ≅ K)
    (θh : U₃.obj (Q.obj (J₁.obj K)) ≅ K)
    (hf : θf.hom ≫ a₁.unit.app K = tf.app (J₁.obj K))
    (hg : θg.hom ≫ a₂.unit.app K = tg.app (J₂.obj K))
    (hh : θh.hom ≫ a₁.unit.app K = th.app (J₁.obj K)) :
    (a₃.homEquiv _ _).symm θh.inv =
      (a₃.homEquiv _ _).symm θg.inv ≫
        S.map ((a₂.homEquiv _ _).symm θf.inv) ≫ c.hom.app (J₁.obj K) := by
  apply (a₃.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono θh.hom).mp
  apply (cancel_mono (a₁.unit.app K)).mp
  simp only [Category.assoc, hh]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hn := tg.naturality ((a₂.homEquiv _ _).symm θf.inv)
  simp only [Functor.comp_map] at hn
  rw [ht, reassoc_of% hn]
  rw [← hg]
  simp only [← Category.assoc]
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, Iso.inv_hom_id,
    Category.id_comp]
  simp only [Category.assoc]
  rw [← hf]
  simp only [← Category.assoc]
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, Iso.inv_hom_id,
    Category.id_comp]
  simp [← hh]

/-- The canonical composition identification for bounded below derived direct images.
It derives the fibre-product-pasting isomorphism `lowerStarComp` on injectives.
The injective-preservation structure comes from the exact inverse-image adjunction. -/
noncomputable def properOpenDirectImageCompIso (Λ : Type (u + 1)) [CommRing Λ]
    {T₁ T₂ T₃ : Scheme.{u}} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g ≅
      rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (f ≫ g) := by
  letI : (lowerStar (ModuleCat.{u + 1} Λ) f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  exact Functor.rightDerivedFunctorPlusCompIso'
    (lowerStar (ModuleCat.{u + 1} Λ) f) (lowerStar (ModuleCat.{u + 1} Λ) g)
    (lowerStarComp (ModuleCat.{u + 1} Λ) f g)

/-- Proper-open comparisons compose, using the canonical derived direct-image identification,
for any commutative coefficient ring `Λ`. -/
theorem properOpenComparisonOfCommRing_comp (Λ : Type (u + 1)) [CommRing Λ]
    {T₁ T₂ T₃ X : Scheme.{u}} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
    [IsProper f] [IsProper g]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (hf : j₁ ≫ f = j₂) (hg : j₂ ≫ g = j₃)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenComparisonOfCommRing Λ (f ≫ g) j₁ j₃
        ((Category.assoc j₁ f g).symm.trans ((congrArg (· ≫ g) hf).trans hg)) K =
      properOpenComparisonOfCommRing Λ g j₂ j₃ hg K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g).map
          (properOpenComparisonOfCommRing Λ f j₁ j₂ hf K) ≫
        (properOpenDirectImageCompIso Λ f g).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K) := by
  let A := ModuleCat.{u + 1} Λ
  let U₁ := (upperStar A j₁).mapDerivedCategoryPlus
  let U₂ := (upperStar A j₂).mapDerivedCategoryPlus
  let U₃ := (upperStar A j₃).mapDerivedCategoryPlus
  let a₁ := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j₁
  let a₂ := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j₂
  let a₃ := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus A j₃
  let adjF := (upperStarLowerStarAdjunction A f).derivedPlus
  let adjG := (upperStarLowerStarAdjunction A g).derivedPlus
  let adjH := (upperStarLowerStarAdjunction A (f ≫ g)).derivedPlus
  let kf := upperStarCompDerivedPlus A j₁ f j₂ hf.symm
  let kg := upperStarCompDerivedPlus A j₂ g j₃ hg.symm
  let hfg := (Category.assoc j₁ f g).symm.trans ((congrArg (· ≫ g) hf).trans hg)
  let kh := upperStarCompDerivedPlus A j₁ (f ≫ g) j₃ hfg.symm
  let e := upperStarCompDerivedPlus A f g
  let c := properOpenDirectImageCompIso Λ f g
  have hunit (N : DerivedCategory.Plus (Sheaf T₃.smallEtaleTopology A)) :
      (adjG.comp adjF).unit.app N ≫ c.hom.app
          ((upperStar A f).mapDerivedCategoryPlus.obj
            ((upperStar A g).mapDerivedCategoryPlus.obj N)) =
        adjH.unit.app N ≫ (lowerStar A (f ≫ g)).rightDerivedFunctorPlus.map
          (e.hom.app N) := by
    have h := derivedPlus_unit_comp_upperStarCompDerivedPlus A f g (f ≫ g) rfl N
    simpa only [Adjunction.comp_unit_app, Category.assoc, c,
      properOpenDirectImageCompIso, rightDerivedLowerStarPlus] using h.symm
  have hc (M : DerivedCategory.Plus (Sheaf T₁.smallEtaleTopology A)) :
      (upperStar A (f ≫ g)).mapDerivedCategoryPlus.map (c.hom.app M) ≫
          adjH.counit.app M =
        e.hom.app ((lowerStar A g).rightDerivedFunctorPlus.obj
            ((lowerStar A f).rightDerivedFunctorPlus.obj M)) ≫
          (upperStar A f).mapDerivedCategoryPlus.map
            (adjG.counit.app ((lowerStar A f).rightDerivedFunctorPlus.obj M)) ≫
          adjF.counit.app M := by
    simpa only [Adjunction.comp_counit_app, Functor.comp_obj] using
      counit_of_unit (adjG.comp adjF) adjH e.hom c.hom hunit M
  have ha (N : DerivedCategory.Plus (Sheaf T₃.smallEtaleTopology A)) :
      kh.hom.app N ≫ U₁.map (e.hom.app N) =
        kg.hom.app N ≫ kf.hom.app ((upperStar A g).mapDerivedCategoryPlus.obj N) := by
    exact NatTrans.congr_app
      (upperStarCompDerivedPlus_assoc A j₁ f g j₂ (f ≫ g) j₃ hf.symm rfl hg.symm) N
  have hff := a₁.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryPlusCompIso
      (openImmersionLowerShriek A j₁) (upperStar A j₁)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (asIso (openImmersionLowerShriekUpperStarAdjunction A j₁).unit).symm ≪≫
      Functor.mapDerivedCategoryPlusIdIso _)
  have := hff.full
  have := hff.faithful
  have ht := restriction_comp adjF adjG adjH U₁ U₂ U₃ kf kg kh e c ha hc
  exact comparison_comp a₁ a₂ a₃ (lowerStar A f).rightDerivedFunctorPlus
    (lowerStar A g).rightDerivedFunctorPlus (lowerStar A (f ≫ g)).rightDerivedFunctorPlus
    c (restriction adjF U₁ U₂ kf) (restriction adjG U₂ U₃ kg)
    (restriction adjH U₁ U₃ kh) ht K
    (properOpenIdentificationOfCommRing Λ f j₁ j₂ hf K)
    (properOpenIdentificationOfCommRing Λ g j₂ j₃ hg K)
    (properOpenIdentificationOfCommRing Λ (f ≫ g) j₁ j₃ hfg K)
    (properOpenIdentificationOfCommRing_unit Λ f j₁ j₂ hf K)
    (properOpenIdentificationOfCommRing_unit Λ g j₂ j₃ hg K)
    (properOpenIdentificationOfCommRing_unit Λ (f ≫ g) j₁ j₃ hfg K)

/-- The finite-coefficient case of `properOpenComparisonOfCommRing_comp`, kept for its existing
users (`properOpenComparison` is `properOpenComparisonOfCommRing` at a finite ring). -/
theorem properOpenComparison_comp (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ T₃ X : Scheme.{u}} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
    [IsProper f] [IsProper g]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (hf : j₁ ≫ f = j₂) (hg : j₂ ≫ g = j₃)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenComparison Λ (f ≫ g) j₁ j₃
        ((Category.assoc j₁ f g).symm.trans ((congrArg (· ≫ g) hf).trans hg)) K =
      properOpenComparison Λ g j₂ j₃ hg K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g).map
          (properOpenComparison Λ f j₁ j₂ hf K) ≫
        (properOpenDirectImageCompIso Λ f g).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K) :=
  properOpenComparisonOfCommRing_comp Λ f g j₁ j₂ j₃ hf hg K

end AlgebraicGeometry.Etale
