/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueComparisonInterface
import WeilConjectures.AlgebraicGeometry.IntegralResiduePullOrdinaryUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! The counit-normalized mate calculation for the integral residue pull square.

Source: Bhatt--Scholze, Remark 6.8.15.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_agIntegralResiduePullFlatModelMateNormalized
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

-- Private counit and mate calculations retained from the former flat-model proof.
section ProofCalculations
open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section CachedInstances
variable (T : AlgebraicGeometry.Scheme.{u})
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
local notation "M" => Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab)
  (AlgebraicGeometry.ProEtale.condensedRingObj Λ T)
@[instance_reducible]
private noncomputable def cachedProofInstance1 : MonoidalCategory M := inferInstance
private theorem cachedProofInstance2_private : MonoidalPreadditive M := inferInstance

/-- Public export of the private `cachedProofInstance2_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance2 := cachedProofInstance2_private
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance3_private : HasCountableCoproducts M := inferInstance

/-- Public export of the private `cachedProofInstance3_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance3 := cachedProofInstance3_private
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance4_private : HasColimitsOfShape ℤ M := inferInstance

/-- Public export of the private `cachedProofInstance4_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance4 := cachedProofInstance4_private
private theorem cachedProofInstance5_private : Abelian.HasFunctorialFlatResolution M :=
  inferInstance

/-- Public export of the private `cachedProofInstance5_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance5 := cachedProofInstance5_private
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance6_private : Abelian.HasKInjectiveResolutions M := inferInstance

/-- Public export of the private `cachedProofInstance6_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance6 := cachedProofInstance6_private
omit [IsCommMonObj Λ] in
private theorem cachedProofInstance7_private : HasExactColimitsOfShape ℤ M := inferInstance

/-- Public export of the private `cachedProofInstance7_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance7 := cachedProofInstance7_private
private theorem cachedProofInstance8_private : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ M),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance

/-- Public export of the private `cachedProofInstance8_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance8 := cachedProofInstance8_private
private theorem cachedProofInstance9_private : ∀ (X₁ X₂ X₃ : GradedObject ℤ M),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance

/-- Public export of the private `cachedProofInstance9_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance9 := cachedProofInstance9_private
private theorem cachedProofInstance10_private : ∀ (X₁ X₂ X₃ : GradedObject ℤ M),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance

/-- Public export of the private `cachedProofInstance10_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance10 := cachedProofInstance10_private
private theorem cachedProofInstance11_private : ∀ (X : M),
    PreservesColimitsOfShape ℤ ((curriedTensor M).obj X) := inferInstance

/-- Public export of the private `cachedProofInstance11_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance11 := cachedProofInstance11_private
private theorem cachedProofInstance12_private : ∀ (X : M),
    PreservesColimitsOfShape ℤ ((curriedTensor M).flip.obj X) := inferInstance

/-- Public export of the private `cachedProofInstance12_private`
(used by `import all` importers; linter.privateModule). -/
alias cachedProofInstance12 := cachedProofInstance12_private
end CachedInstances
attribute [local instance]
  cachedProofInstance1 cachedProofInstance2_private
  cachedProofInstance3_private cachedProofInstance4_private
  cachedProofInstance5_private cachedProofInstance6_private
  cachedProofInstance7_private cachedProofInstance8_private
  cachedProofInstance9_private cachedProofInstance10_private
  cachedProofInstance11_private cachedProofInstance12_private

private theorem exactSquareFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [Limits.PreservesFiniteLimits I] [Limits.PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (N : HomotopyCategory A (.up ℤ)) :
    (mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryNatIso e ≪≫
      (mapDerivedCategoryCompIso H I).symm).hom.app (DerivedCategory.Qh.obj N) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app N) ≫
        I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app N) := by
  have hF := mapDerivedCategoryCompIso_fach F G N
  have hH := mapDerivedCategoryCompIso_fach H I N
  rw [mapHomotopyCategoryCompIso_refl_hom_app] at hF hH
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hF hH
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hH, mapDerivedCategoryNatIso_fach, ← hF]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem exactSquareFacInv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : H ⋙ I ≅ F ⋙ G) (N : HomotopyCategory A (.up ℤ)) :
    (mapDerivedCategoryCompIso F G ≪≫ (mapDerivedCategoryNatIso e).symm ≪≫
      (mapDerivedCategoryCompIso H I).symm).hom.app (DerivedCategory.Qh.obj N) ≫
        I.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app N) ≫
        I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N) := by
  have h := exactSquareFac F G H I e.symm N
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    mapDerivedCategoryNatIso_symm] using h

private theorem liftedSquareFac
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G G' : B ⥤ D) (H H' : A ⥤ C) (I : C ⥤ D)
    (eG : G' ≅ G) (eH : H' ≅ H) (q : F ⋙ G ≅ H ⋙ I)
    {N : A} {B₀ : B} {C₀ : C} {D₀ D₁ : D}
    (x : F.obj N ⟶ B₀) (u : G.obj B₀ ⟶ D₀)
    (v : H.obj N ⟶ C₀) (r : I.obj C₀ ⟶ D₁) (o : D₀ ⟶ D₁)
    (u' : G'.obj B₀ ⟶ D₀) (v' : H'.obj N ⟶ C₀)
    (hu : eG.hom.app B₀ ≫ u = u') (hv : eH.hom.app N ≫ v = v')
    (hq : q.hom.app N ≫ I.map v ≫ r = G.map x ≫ u ≫ o) :
    (isoWhiskerLeft F eG ≪≫ q ≪≫ isoWhiskerRight eH.symm I).hom.app N ≫
      I.map v' ≫ r =
      G'.map x ≫ u' ≫ o := by
  rw [← hu, ← hv]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← I.map_comp_assoc, Iso.inv_hom_id_app, I.map_id, Category.id_comp, hq]
  rw [← eG.hom.naturality_assoc]

private theorem exactLeftSquareFac_private
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution A]
    [MonoidalCategory B] [MonoidalPreadditive B] [HasCountableCoproducts B]
    [HasColimitsOfShape ℤ B] [HasExactColimitsOfShape ℤ B]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((curriedTensor B).obj X)]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution B]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : H ⋙ I ≅ F ⋙ G) (N : HomotopyCategory A (.up ℤ)) :
    (isoWhiskerLeft F.mapDerivedCategory G.leftDerivedFunctorIsoMapDerivedCategory ≪≫
      ((mapDerivedCategoryCompIso F G) ≪≫ (mapDerivedCategoryNatIso e).symm ≪≫
        (mapDerivedCategoryCompIso H I).symm) ≪≫
      isoWhiskerRight H.leftDerivedFunctorIsoMapDerivedCategory.symm
        I.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj N) ≫
      I.mapDerivedCategory.map (H.leftDerivedFunctorCounit.app N) ≫
      I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N) =
    G.leftDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
      G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N) := by
  have hG := NatTrans.congr_app G.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj N)
  have hH := NatTrans.congr_app H.leftDerivedFunctorIsoMapDerivedCategory_hom_fac N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hG hH
  exact liftedSquareFac F.mapDerivedCategory G.mapDerivedCategory
    G.leftDerivedFunctor H.mapDerivedCategory H.leftDerivedFunctor I.mapDerivedCategory
    G.leftDerivedFunctorIsoMapDerivedCategory H.leftDerivedFunctorIsoMapDerivedCategory
    ((mapDerivedCategoryCompIso F G) ≪≫ (mapDerivedCategoryNatIso e).symm ≪≫
      (mapDerivedCategoryCompIso H I).symm)
    (F.mapDerivedCategoryFactorsh.hom.app N)
    (G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N))
    (H.mapDerivedCategoryFactorsh.hom.app N)
    (I.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj N))
    (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app N))
    (G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (.up ℤ)).obj N))
    (H.leftDerivedFunctorCounit.app N) hG hH (exactSquareFacInv F G H I e N)

/-- Public export of the private `exactLeftSquareFac_private`
(used by `import all` importers; linter.privateModule). -/
alias exactLeftSquareFac := exactLeftSquareFac_private

private theorem transportedUnitFac
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R S : B ⥤ A} (ad : L ⊣ R) (e : R ≅ S)
    {X Z : A} {Y : B} (a : L.obj X ⟶ Y) (s : S.obj Y ≅ Z)
    (u : X ⟶ Z) (v : Z ⟶ R.obj Y)
    (hu : ad.unit.app X ≫ R.map a = u ≫ v)
    (hv : v ≫ e.hom.app Y = s.inv) :
    (ad.ofNatIsoRight e).unit.app X ≫ S.map a ≫ s.hom = u := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality_assoc, ← Category.assoc, hu]
  simp only [Category.assoc]
  rw [reassoc_of% hv, Iso.inv_hom_id, Category.comp_id]

private theorem mixedDerivedUnitFac_private
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive]
    [F.PreservesKFlatQuasiIso] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : F ⊣ R) (H : HomotopyCategory C (.up ℤ)) :
    (adj.derivedAdjunction.ofNatIsoRight R.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Qh.obj H) ≫
      R.mapDerivedCategory.map (F.leftDerivedFunctorCounit.app H) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj H) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app H) := by
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (L₁ := DerivedCategory.Qh) (L₂ := DerivedCategory.Qh)
    (G' := F.leftDerivedFunctor) (F' := R.rightDerivedFunctor)
    (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit
    R.rightDerivedFunctorUnit H
  have h₃ := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj H)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  exact transportedUnitFac adj.derivedAdjunction
    R.rightDerivedFunctorIsoMapDerivedCategory (F.leftDerivedFunctorCounit.app H)
    (R.mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory (.up ℤ)).obj H))
    (DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app H))
    (R.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj H)) h₁ h₃

/-- Public export of the private `mixedDerivedUnitFac_private`
(used by `import all` importers; linter.privateModule). -/
alias mixedDerivedUnitFac := mixedDerivedUnitFac_private

private theorem mateModel_private
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LX : C ⥤ D} {RX : D ⥤ C} {LY : C' ⥤ D'} {RY : D' ⥤ C'}
    (adX : LX ⊣ RX) (adY : LY ⊣ RY)
    (U : C' ⥤ C) (V : D' ⥤ D) (q : RY ⋙ U ⟶ V ⋙ RX)
    {K : C'} {A Z₀ Z₁ Z₂ : C} {B : D'} {T₀ T₁ : D} {W : C'}
    (u : U.obj K ⟶ A) (a : LX.obj A ⟶ T₀) (o : T₀ ⟶ T₁)
    (s : LY.obj K ⟶ B) (v : V.obj B ⟶ T₁)
    (r₀ : RX.obj T₀ ⟶ Z₀) (r₁ : RX.obj T₁ ⟶ Z₁) [IsIso r₁]
    (w : RY.obj B ⟶ W) (t : U.obj W ⟶ Z₂) (qo : Z₂ ⟶ Z₁)
    (η₀ : A ⟶ Z₀) (η₁ : K ⟶ W) (on : Z₀ ⟶ Z₁)
    (hηX : adX.unit.app A ≫ RX.map a ≫ r₀ = η₀)
    (hηY : adY.unit.app K ≫ RY.map s ≫ w = η₁)
    (ho : RX.map o ≫ r₁ = r₀ ≫ on)
    (hq : q.app B ≫ RX.map v ≫ r₁ = U.map w ≫ t ≫ qo)
    (hOrd : u ≫ η₀ ≫ on = U.map η₁ ≫ t ≫ qo) :
    LX.map u ≫ a ≫ o =
      (((mateEquiv adY adX).symm (TwoSquare.mk _ _ _ _ q)).app K) ≫
        V.map s ≫ v := by
  apply (adX.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono r₁).1
  have hm := unit_mateEquiv_symm adY adX (TwoSquare.mk _ _ _ _ q) K
  change U.map (adY.unit.app K) ≫ q.app (LY.obj K) =
    adX.unit.app (U.obj K) ≫ RX.map
      (((mateEquiv adY adX).symm (TwoSquare.mk _ _ _ _ q)).app K) at hm
  rw [← reassoc_of% adX.unit.naturality u]
  simp only [comp_obj]
  rw [← reassoc_of% hm]
  have hn := q.naturality s
  dsimp only [Functor.comp_map, comp_obj] at hn
  simp only [Category.assoc]
  rw [ho]
  rw [reassoc_of% hηX]
  rw [← reassoc_of% hn, hq]
  rw [← U.map_comp_assoc, ← U.map_comp_assoc, Category.assoc, hηY]
  exact hOrd

/-- Public export of the private `mateModel_private`
(used by `import all` importers; linter.privateModule). -/
alias mateModel := mateModel_private

private theorem naturalOrdinaryFac_private
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {Q : A ⥤ B} {F : A ⥤ C} {G : B ⥤ D} {R : C ⥤ D}
    (c : Q ⋙ G ⟶ F ⋙ R) {X Y : A} {Z W : C}
    (η : X ⟶ Y) (ηX : F.obj X ⟶ Z) (on : Z ⟶ W) (qo : F.obj Y ⟶ W)
    (h : F.map η ≫ qo = ηX ≫ on) :
    c.app X ≫ R.map ηX ≫ R.map on =
      G.map (Q.map η) ≫ c.app Y ≫ R.map qo := by
  have hn := c.naturality η
  dsimp only [Functor.comp_map] at hn
  rw [← R.map_comp, ← h, R.map_comp, ← Category.assoc, ← hn, Category.assoc]

/-- Public export of the private `naturalOrdinaryFac_private`
(used by `import all` importers; linter.privateModule). -/
alias naturalOrdinaryFac := naturalOrdinaryFac_private

namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing
end ProofCalculations

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
end AlgebraicGeometry.ProEtale.CondensedRing
