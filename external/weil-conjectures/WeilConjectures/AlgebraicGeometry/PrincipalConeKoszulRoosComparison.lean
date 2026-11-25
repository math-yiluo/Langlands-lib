/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.AlgebraicGeometry.PrincipalKoszulRoosPresentationComparison
import all WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import all WeilConjectures.AlgebraicGeometry.FiniteFreeQuotientTower
import all WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
/-! # The normalized scalar cone and tensor Koszul Roos comparison

Source: Stacks 0A0E and 0941.
(auxiliary; not a blueprint node).

The finite tensor-cone comparison is kept behind its naturality and inclusion lemmas,
so type checking does not repeatedly expand the total tensor construction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
-- As in FiniteFreeQuotientTower, avoid expanding dependent total-tensor transports
-- solely to check unused section variables.
set_option linter.unusedVariables false
set_option maxErrors 4
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open HomologicalComplex CochainComplex.HomComplex
open scoped ChangeOfRings
private def normalizedCoconeLift
    {B : Type*} [Category* B] [Abelian B] {P X Y : CochainComplex B ℤ}
    (f : X ⟶ Y) (a : P ⟶ X) (h : a ≫ f = 0) :
    P ⟶ CochainComplex.mappingCocone f :=
  CochainComplex.mappingCocone.lift f a 0 (by simp [h])

private theorem towerAugmentationCondition
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    {P : CochainComplex B ℤ} (T : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    Pi.lift (fun n ↦ γ.app (op n)) ≫ towerTransitionEndomorphism
      (K := fun n ↦ T.obj (op n)) (WeilConjectures.integralOperationsTowerStep T) = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, Preadditive.comp_sub, Category.comp_id,
    Preadditive.sub_comp, towerProductShift, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
    zero_comp]
  apply sub_eq_zero.mpr
  change γ.app (op n) = γ.app (op (n + 1)) ≫ T.map (homOfLE (Nat.le_succ n)).op
  exact (Category.id_comp _).symm.trans (γ.naturality (homOfLE (Nat.le_succ n)).op)

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedConeComparison
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    [HasDerivedCategory B]
    {P : CochainComplex B ℤ} (μ : End P) (T : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (a : ∀ n, CochainComplex.PrincipalCone.level μ n ≅ T.obj (op n))
    (hs : ∀ n, CochainComplex.PrincipalCone.step μ n ≫ (a n).hom =
      (a (n + 1)).hom ≫ WeilConjectures.integralOperationsTowerStep T n)
    (hu : ∀ n, CochainComplex.mappingCone.inr (μ ^ (n + 1)).asHom ≫ (a n).hom =
      γ.app (op n)) :
    ∃ c : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion μ) ≅
        DerivedCategory.Q.obj (WeilConjectures.integralOperationsRoos T),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫ c.hom =
        DerivedCategory.Q.map (normalizedCoconeLift _ (Pi.lift (fun n ↦ γ.app (op n)))
          (towerAugmentationCondition T γ)) := by
  classical
  let u := fun n ↦ γ.app (op n)
  have hv := towerAugmentationCondition T γ
  let p : (∏ᶜ fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)) ≅
      ∏ᶜ (fun n ↦ T.obj (op n)) := Pi.mapIso a
  let f := CochainComplex.PrincipalCone.oneSubShift μ
  let g := towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
    (WeilConjectures.integralOperationsTowerStep T)
  have hfg : f ≫ p.hom = p.hom ≫ g :=
    (towerTransitionEndomorphism_natural_backward
      (K := fun n ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n))
      (K' := fun n ↦ T.obj (op n))
      (CochainComplex.PrincipalCone.step μ)
      (WeilConjectures.integralOperationsTowerStep T) (fun n ↦ (a n).hom)
      (fun n ↦ (hs n).symm)).symm
  let i := (shiftFunctor _ (-1 : ℤ)).mapIso
    (CochainComplex.coneSquareIso f g p p hfg)
  have hn : (𝟙 P) ≫ Pi.lift u = CochainComplex.PrincipalCone.productUnit μ ≫ p.hom := by
    apply Pi.hom_ext
    intro n
    simp only [Category.id_comp, p, Category.assoc, Pi.mapIso_hom_π,
      CochainComplex.PrincipalCone.productUnit, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    exact (hu n).symm
  refine ⟨DerivedCategory.Q.mapIso i, ?_⟩
  change DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit μ) ≫
    DerivedCategory.Q.map i.hom = _
  rw [← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  simpa only [Category.id_comp, CochainComplex.PrincipalCone.unit,
    normalizedCoconeLift, i, Functor.mapIso_hom, CochainComplex.coneSquareIso,
    CochainComplex.mappingCocone, f, g, u] using
    (completedCoconeLift_natural B f g p.hom p.hom hfg (𝟙 P)
      (CochainComplex.PrincipalCone.productUnit μ) (Pi.lift u)
      (CochainComplex.PrincipalCone.productUnit_comp μ) hv hn).symm

namespace CochainComplex
variable {B C D : Type*} [Category* B] [Category* C] [Category* D]
  [Preadditive B] [HasBinaryBiproducts B] [HasZeroMorphisms C] [Preadditive D]
    [HasBinaryBiproducts D]
  (F : B ⥤ C ⥤ D) [F.Additive] [∀ X, (F.obj X).PreservesZeroMorphisms]
  (P : CochainComplex C ℤ)
  [∀ X : CochainComplex B ℤ, HomologicalComplex.HasMapBifunctor X P F (.up ℤ)]

omit [HasBinaryBiproducts D] in
private theorem tensorInl_natural
    {X Y X' Y' : CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) (n : ℤ) :
    (mapBifunctorMap a (𝟙 P) F (.up ℤ)).f (n + 1) ≫
        (mapBifunctorMappingCone₁Iso.ι₁ g P F).v (n + 1) n (by omega) =
      (mapBifunctorMappingCone₁Iso.ι₁ f P F).v (n + 1) n (by omega) ≫
        (mapBifunctorMap (mappingCone.map f g a b h) (𝟙 P) F (.up ℤ)).f n := by
  ext p q hpq
  dsimp at hpq
  simp [mapBifunctorMappingCone₁Iso.ι_ι₁_assoc
    f P F p q (n + 1) hpq n (by omega) (p - 1) (by omega),
    mapBifunctorMappingCone₁Iso.ι_ι₁
      g P F p q (n + 1) hpq n (by omega) (p - 1) (by omega),
    mappingCone.map, ← Functor.map_comp, ← NatTrans.comp_app_assoc]

private theorem tensorCone_inv_natural
    {X Y X' Y' : CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (h' : mapBifunctorMap f (𝟙 P) F (.up ℤ) ≫
        mapBifunctorMap b (𝟙 P) F (.up ℤ) =
      mapBifunctorMap a (𝟙 P) F (.up ℤ) ≫
        mapBifunctorMap g (𝟙 P) F (.up ℤ)) :
    mappingCone.map _ _ (mapBifunctorMap a (𝟙 P) F (.up ℤ))
        (mapBifunctorMap b (𝟙 P) F (.up ℤ)) h' ≫
        (mapBifunctorMappingCone₁Iso g P F).inv =
      (mapBifunctorMappingCone₁Iso f P F).inv ≫
        mapBifunctorMap (mappingCone.map f g a b h) (𝟙 P) F (.up ℤ) := by
  ext n
  apply mappingCone.ext_from _ (n + 1) n rfl
  · simpa [mappingCone.map, mapBifunctorMappingCone₁Iso,
      mapBifunctorMappingCone₁Iso.inv] using tensorInl_natural F P f g a b h n
  · simp only [mappingCone.map, mapBifunctorMappingCone₁Iso,
      mapBifunctorMappingCone₁Iso.inv]
    ext p q hpq
    simp [← Functor.map_comp, ← NatTrans.comp_app_assoc]

end CochainComplex

private def genericTensorConeIso
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [Preadditive B] [HasBinaryBiproducts B] [HasZeroMorphisms C] [Preadditive D]
      [HasBinaryBiproducts D]
    (F : B ⥤ C ⥤ D) [F.Additive]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ (X : CochainComplex B ℤ) (Y : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor X Y F (.up ℤ)]
    (P : CochainComplex C ℤ) {X Y : CochainComplex B ℤ} (f : X ⟶ Y) :
    (F.map₂CochainComplex.flip.obj P).obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone ((F.map₂CochainComplex.flip.obj P).map f) :=
  CochainComplex.mapBifunctorMappingCone₁Iso f P F

private theorem genericTensorConeIso_natural
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [Preadditive B] [HasBinaryBiproducts B] [HasZeroMorphisms C] [Preadditive D]
      [HasBinaryBiproducts D]
    (F : B ⥤ C ⥤ D) [F.Additive]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ (X : CochainComplex B ℤ) (Y : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor X Y F (.up ℤ)]
    (P : CochainComplex C ℤ)
    {X Y X' Y' : CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (h' : (F.map₂CochainComplex.flip.obj P).map f ≫
        (F.map₂CochainComplex.flip.obj P).map b =
      (F.map₂CochainComplex.flip.obj P).map a ≫
        (F.map₂CochainComplex.flip.obj P).map g) :
    CochainComplex.mappingCone.map _ _ ((F.map₂CochainComplex.flip.obj P).map a)
        ((F.map₂CochainComplex.flip.obj P).map b) h' ≫
        (genericTensorConeIso F P g).inv =
      (genericTensorConeIso F P f).inv ≫ (F.map₂CochainComplex.flip.obj P).map
        (CochainComplex.mappingCone.map f g a b h) := by
  exact CochainComplex.tensorCone_inv_natural F P f g a b h h'

private theorem genericTensorConeIso_inr
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [Preadditive B] [HasBinaryBiproducts B] [HasZeroMorphisms C] [Preadditive D]
      [HasBinaryBiproducts D]
    (F : B ⥤ C ⥤ D) [F.Additive]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ (X : CochainComplex B ℤ) (Y : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor X Y F (.up ℤ)]
    (P : CochainComplex C ℤ) {X Y : CochainComplex B ℤ} (f : X ⟶ Y) :
    (F.map₂CochainComplex.flip.obj P).map (CochainComplex.mappingCone.inr f) ≫
      (genericTensorConeIso F P f).hom =
        CochainComplex.mappingCone.inr ((F.map₂CochainComplex.flip.obj P).map f) := by
  exact CochainComplex.mapBifunctorMap_inr_mapBifunctorMappingCone₁Iso_hom f P F

section TensorConeFunctor
variable {B C D : Type*} [Category* B] [Category* C] [Category* D]
  [Preadditive B] [HasBinaryBiproducts B] [HasZeroMorphisms C] [Preadditive D]
    [HasBinaryBiproducts D]
  (F : B ⥤ C ⥤ D) [F.Additive]
  [∀ X, (F.obj X).PreservesZeroMorphisms]
  [∀ (X : CochainComplex B ℤ) (Y : CochainComplex C ℤ),
    HomologicalComplex.HasMapBifunctor X Y F (.up ℤ)]
  (P : CochainComplex C ℤ) (G : CochainComplex B ℤ ⥤ CochainComplex D ℤ)
  (hG : G = F.map₂CochainComplex.flip.obj P)

@[irreducible] private def tensorConeData
    {X Y : CochainComplex B ℤ} (f : X ⟶ Y) :
    G.obj (CochainComplex.mappingCone f) ≅ CochainComplex.mappingCone (G.map f) := by
  subst G
  exact genericTensorConeIso F P f

private theorem tensorConeData_inr
    {X Y : CochainComplex B ℤ} (f : X ⟶ Y) :
    G.map (CochainComplex.mappingCone.inr f) ≫ (tensorConeData F P G hG f).hom =
      CochainComplex.mappingCone.inr (G.map f) := by
  subst G
  unfold tensorConeData
  exact genericTensorConeIso_inr F P f

private theorem tensorConeData_natural
    {X Y X' Y' : CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (h' : G.map f ≫ G.map b = G.map a ≫ G.map g) :
    CochainComplex.mappingCone.map _ _ (G.map a) (G.map b) h' ≫
        (tensorConeData F P G hG g).inv =
      (tensorConeData F P G hG f).inv ≫
        G.map (CochainComplex.mappingCone.map f g a b h) := by
  subst G
  unfold tensorConeData
  exact genericTensorConeIso_natural F P f g a b h h'
end TensorConeFunctor

attribute [local irreducible] genericTensorConeIso

namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
private theorem cacheSheafCompose (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
attribute [local instance 20000] cacheSheafCompose

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem moduleSheafify : HasSheafify J AddCommGrpCat.{u} := inferInstance
private theorem moduleLocallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance
attribute [local instance 20000] moduleSheafify moduleLocallyBijective
variable (R : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "𝒜" => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local instance] tensorPreadditive tensorAdditive quotientUnitInclusionIso
@[reducible] private instance chosenMonoidal : MonoidalCategory 𝒜 :=
  SheafOfModules.monoidalCategory R
attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem moduleBiproducts : HasBinaryBiproducts 𝒜 := inferInstance
attribute [local instance 1100] moduleBiproducts

private theorem moduleCountableProducts : HasCountableProducts 𝒜 := inferInstance
private theorem moduleSmallDiscreteColimits (ι : Type) :
    HasColimitsOfShape (Discrete ι) 𝒜 := inferInstance
attribute [local instance 20000] moduleCountableProducts moduleSmallDiscreteColimits

private lemma endoPow_eq_pow {B : Type*} [Category* B] {X : B}
    (f : End X) (n : ℕ) : endoPow f.asHom n = (f ^ n).asHom := by
  induction n with
  | zero => rfl
  | succ n ih => rw [endoPow, ih, pow_succ']; rfl

private lemma quotientAction_eq (P : CochainComplex 𝒜 ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (n : ℕ) : quotientAction R P a n = endoPow (quotientAction R P a 0) (n + 1) := by
  unfold quotientAction
  let G := CochainComplex.singleFunctor 𝒜 0 ⋙ koszulTensorFunctor R P
  change (quotientUnitIso R P).hom ≫
    G.map (endoPow (globalSectionMultiplication R a) (n + 1)) ≫
      (quotientUnitIso R P).inv = _
  apply (conjugatedMapPow G (quotientUnitIso R P)
    (globalSectionMultiplication R a) (n + 1)).trans
  congr 1

private def coneSquareIso {B : Type*} [Category* B] [Preadditive B] [HasBinaryBiproducts B]
    {P Q P' Q' : CochainComplex B ℤ} (f : P ⟶ Q) (g : P' ⟶ Q')
    (a : P ≅ P') (b : Q ≅ Q') (h : f ≫ b.hom = a.hom ≫ g) :
    CochainComplex.mappingCone f ≅ CochainComplex.mappingCone g where
  hom := CochainComplex.mappingCone.map f g a.hom b.hom h
  inv := CochainComplex.mappingCone.map g f a.inv b.inv (by
    rw [← cancel_epi a.hom, ← cancel_mono b.hom]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, h])
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact CochainComplex.mappingCone.map_id f
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact CochainComplex.mappingCone.map_id g

private def functorConeConjugate {B : Type*} [Category* B] [Preadditive B] [HasBinaryBiproducts B]
    (G : CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    {P X : CochainComplex B ℤ} (α : P ⟶ P) (f : X ⟶ X) (e : P ≅ G.obj X)
    (h : α ≫ e.hom = e.hom ≫ G.map f)
    (i : G.obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone (G.map f)) :
    CochainComplex.mappingCone α ≅ G.obj (CochainComplex.mappingCone f) :=
  coneSquareIso α (G.map f) e e h ≪≫ i.symm

private theorem functorConeConjugate_inr {B : Type*} [Category* B] [Preadditive B]
  [HasBinaryBiproducts B]
    (G : CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    {P X : CochainComplex B ℤ} (α : P ⟶ P) (f : X ⟶ X) (e : P ≅ G.obj X)
    (h : α ≫ e.hom = e.hom ≫ G.map f)
    (i : G.obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone (G.map f))
    (hi : G.map (CochainComplex.mappingCone.inr f) ≫ i.hom =
      CochainComplex.mappingCone.inr (G.map f)) :
    CochainComplex.mappingCone.inr α ≫ (functorConeConjugate G α f e h i).hom =
      e.hom ≫ G.map (CochainComplex.mappingCone.inr f) := by
  apply (cancel_mono i.hom).mp
  simp only [functorConeConjugate, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, hi]
  simp [coneSquareIso, CochainComplex.mappingCone.map]

private theorem functorConeConjugate_natural {B : Type*} [Category* B] [Preadditive B]
  [HasBinaryBiproducts B]
    (G : CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    {P X : CochainComplex B ℤ} (α₁ α₂ : P ⟶ P) (f₁ f₂ : X ⟶ X)
    (e : P ≅ G.obj X) (a : P ⟶ P) (b : X ⟶ X)
    (h₁ : α₁ ≫ e.hom = e.hom ≫ G.map f₁)
    (h₂ : α₂ ≫ e.hom = e.hom ≫ G.map f₂)
    (ha : a ≫ e.hom = e.hom ≫ G.map b)
    (hs : α₂ ≫ 𝟙 _ = a ≫ α₁) (ht : f₂ ≫ 𝟙 _ = b ≫ f₁)
    (i₁ : G.obj (CochainComplex.mappingCone f₁) ≅ CochainComplex.mappingCone (G.map f₁))
    (i₂ : G.obj (CochainComplex.mappingCone f₂) ≅ CochainComplex.mappingCone (G.map f₂))
    (hn : CochainComplex.mappingCone.map (G.map f₂) (G.map f₁) (G.map b) (𝟙 _)
        (by rw [← G.map_id X, ← G.map_comp, ← G.map_comp, ht]) ≫ i₁.inv =
      i₂.inv ≫ G.map (CochainComplex.mappingCone.map f₂ f₁ b (𝟙 _) ht)) :
    CochainComplex.mappingCone.map α₂ α₁ a (𝟙 _) hs ≫
        (functorConeConjugate G α₁ f₁ e h₁ i₁).hom =
      (functorConeConjugate G α₂ f₂ e h₂ i₂).hom ≫
        G.map (CochainComplex.mappingCone.map f₂ f₁ b (𝟙 _) ht) := by
  unfold functorConeConjugate
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← hn, ← Category.assoc, ← Category.assoc]
  congr 1
  unfold coneSquareIso
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  simp only [Category.id_comp, Category.comp_id, ha]

private instance tensorTotal (X Y : CochainComplex 𝒜 ℤ) :
    HomologicalComplex.HasMapBifunctor X Y (curriedTensor 𝒜) (.up ℤ) :=
  fun j ↦ (inferInstance : HasColimitsOfShape
    (Discrete {p : ℤ × ℤ // p.1 + p.2 = j}) 𝒜).has_colimit _

attribute [local irreducible] koszulTensorFunctor globalSectionMultiplication

@[irreducible] private def tensorConeIso (P : CochainComplex 𝒜 ℤ)
    {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y) :
    (koszulTensorFunctor R P).obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone ((koszulTensorFunctor R P).map f) :=
  tensorConeData (curriedTensor 𝒜) P (koszulTensorFunctor R P)
    (by unfold koszulTensorFunctor; rfl) f

private theorem tensorConeIso_inr (P : CochainComplex 𝒜 ℤ)
    {X Y : CochainComplex 𝒜 ℤ} (f : X ⟶ Y) :
    (koszulTensorFunctor R P).map (CochainComplex.mappingCone.inr f) ≫
      (tensorConeIso R P f).hom =
        CochainComplex.mappingCone.inr ((koszulTensorFunctor R P).map f) := by
  unfold tensorConeIso
  exact tensorConeData_inr (curriedTensor 𝒜) P (koszulTensorFunctor R P) _ f

private theorem tensorConeIso_natural (P : CochainComplex 𝒜 ℤ)
    {X Y X' Y' : CochainComplex 𝒜 ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (h' : (koszulTensorFunctor R P).map f ≫ (koszulTensorFunctor R P).map b =
      (koszulTensorFunctor R P).map a ≫ (koszulTensorFunctor R P).map g) :
    CochainComplex.mappingCone.map _ _ ((koszulTensorFunctor R P).map a)
        ((koszulTensorFunctor R P).map b) h' ≫ (tensorConeIso R P g).inv =
      (tensorConeIso R P f).inv ≫ (koszulTensorFunctor R P).map
        (CochainComplex.mappingCone.map f g a b h) := by
  unfold tensorConeIso
  exact tensorConeData_natural (curriedTensor 𝒜) P (koszulTensorFunctor R P) _
    f g a b h h'

private theorem action_conjugacy (P : CochainComplex 𝒜 ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) (n : ℕ) :
    CategoryTheory.End.asHom (CategoryTheory.End.of (quotientAction R P a 0) ^ (n + 1)) ≫
      (quotientUnitIso R P).hom =
      (quotientUnitIso R P).hom ≫ (koszulTensorFunctor R P).map
        (principalKoszulScalarComplex R a n) := by
  unfold principalKoszulScalarComplex
  rw [← endoPow_eq_pow, ← quotientAction_eq]
  unfold quotientAction
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[irreducible] private def qConeIso (P : CochainComplex 𝒜 ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) (n : ℕ) :
    CochainComplex.PrincipalCone.level (A := 𝒜) (P := P) (End.of (quotientAction R P a 0)) n ≅
      (koszulTensorFunctor R P).obj (principalKoszul R a n) := by
  let G := koszulTensorFunctor R P
  let f := principalKoszulScalarComplex R a n
  change CochainComplex.mappingCone _ ≅ G.obj (CochainComplex.mappingCone f)
  apply functorConeConjugate G _ f (quotientUnitIso R P) (action_conjugacy R P a n)
  exact tensorConeIso R P f

private theorem qConeIso_inr (P : CochainComplex 𝒜 ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) (n : ℕ) :
    CochainComplex.mappingCone.inr (CategoryTheory.End.asHom (CategoryTheory.End.of
      (quotientAction R P a 0) ^ (n + 1))) ≫
      (qConeIso R P a n).hom = (quotientUnitIso R P).hom ≫
        (koszulTensorFunctor R P).map
          (show (CochainComplex.singleFunctor 𝒜 0).obj (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⟶
              principalKoszul R a n from CochainComplex.mappingCone.inr _) := by
  unfold qConeIso
  apply functorConeConjugate_inr
  exact tensorConeIso_inr R P _

private theorem qConeIso_step (P : CochainComplex 𝒜 ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections) (n : ℕ) :
    CochainComplex.PrincipalCone.step (A := 𝒜) (P := P) (End.of (quotientAction R P a 0)) n ≫
      (qConeIso R P a n).hom =
        (qConeIso R P a (n + 1)).hom ≫
          (koszulTensorFunctor R P).map (principalKoszulTransition R a n) := by
  let G := koszulTensorFunctor R P
  let S := CochainComplex.singleFunctor 𝒜 0
  let f := principalKoszulScalarComplex R a (n + 1)
  let g := principalKoszulScalarComplex R a n
  let b := S.map (globalSectionMultiplication R a)
  have ha : quotientAction R P a 0 ≫ (quotientUnitIso R P).hom =
      (quotientUnitIso R P).hom ≫ G.map b := by
    simpa only [principalKoszulScalarComplex, Nat.zero_add, pow_one, endoPow,
      Category.id_comp] using action_conjugacy R P a 0
  unfold qConeIso CochainComplex.PrincipalCone.step
  apply functorConeConjugate_natural
  · exact ha
  · have ht := tensorConeIso_natural R P f g b (𝟙 _)
      (principalKoszul_transition_square R a n) (by
        rw [← G.map_comp, ← G.map_comp]
        exact congrArg G.map (principalKoszul_transition_square R a n))
    simpa only [CategoryTheory.Functor.map_id] using ht

-- Fix the degreewise product instance before mentioning a concrete tower.
private instance (priority := 1100) complexProduct (H : ℕ → CochainComplex 𝒜 ℤ) :
    HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete ℕ) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{u} (D := Discrete ℕ)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).has_limit
        (Discrete.functor H)

-- Compare the two strict Roos presentations while the tower is abstract.
-- This prevents conversion from inspecting the total tensor complex in the application.
private def roosModelIso (T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ) :
    WeilConjectures.integralOperationsRoos T ≅ (roosF (A := 𝒜)).obj (koszulTowerComplex R T) :=
  Iso.refl _

private theorem roosModelIso_unit (P : CochainComplex 𝒜 ℤ)
    (T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ) (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (hz : Pi.lift (fun n ↦ γ.app (op n)) ≫ towerTransitionEndomorphism
      (K := fun n ↦ T.obj (op n)) (WeilConjectures.integralOperationsTowerStep T) = 0) :
    normalizedCoconeLift (B := 𝒜) (P := P)
        (towerTransitionEndomorphism (K := fun n ↦ T.obj (op n))
          (WeilConjectures.integralOperationsTowerStep T))
        (Pi.lift (fun n ↦ γ.app (op n))) hz ≫ (roosModelIso R T).hom = principalTowerRoosUnit R P
          T γ := by
  dsimp only [roosModelIso, Iso.refl_hom]
  erw [Category.comp_id]
  rfl

attribute [local irreducible] roosModelIso

attribute [local irreducible] roosF koszulTowerComplex koszulTensorTower
  principalKoszulRoosUnit CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit

variable [HasDerivedCategory.{w} 𝒜]

private theorem coneTowerRoosComparison
    {P : CochainComplex 𝒜 ℤ} (μ : End P) (T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (a : ∀ n, CochainComplex.PrincipalCone.level (A := 𝒜) (P := P) μ n ≅ T.obj (op n))
    (hs : ∀ n, CochainComplex.PrincipalCone.step (A := 𝒜) (P := P) μ n ≫ (a n).hom =
      (a (n + 1)).hom ≫ WeilConjectures.integralOperationsTowerStep T n)
    (hu : ∀ n, CochainComplex.mappingCone.inr (μ ^ (n + 1)).asHom ≫ (a n).hom =
      γ.app (op n)) :
    ∃ e : (DerivedCategory.Q.{w} (C := 𝒜)).obj (CochainComplex.PrincipalCone.completion (A := 𝒜)
      (P := P) μ) ≅
        (DerivedCategory.Q.{w} (C := 𝒜)).obj ((roosF (A := 𝒜)).obj (koszulTowerComplex R T)),
      (DerivedCategory.Q.{w} (C := 𝒜)).map (CochainComplex.PrincipalCone.unit (A := 𝒜) (P := P) μ)
        ≫ e.hom =
        (DerivedCategory.Q.{w} (C := 𝒜)).map (principalTowerRoosUnit R P T γ) := by
  obtain ⟨e, he⟩ := normalizedConeComparison.{u, u + 1, w} (B := 𝒜) (P := P) μ T γ a hs hu
  let d := (DerivedCategory.Q (C := 𝒜)).mapIso (roosModelIso R T)
  refine ⟨e ≪≫ d, ?_⟩
  change _ ≫ e.hom ≫ (DerivedCategory.Q (C := 𝒜)).map (roosModelIso R T).hom = _
  rw [← Category.assoc, he]
  erw [← Functor.map_comp]
  apply congrArg (DerivedCategory.Q (C := 𝒜)).map
  exact roosModelIso_unit R P T γ (towerAugmentationCondition T γ)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The scalar cone completion and the tensor Koszul Roos model have the same unit.

Source: Stacks 0A0E and 0941.
(auxiliary; not a blueprint node).

Proof: tensoring a mapping cone with P commutes with that mapping cone, including
its two inclusions. The unit-tensor isomorphism conjugates scalar multiplication
on P to tensoring scalar multiplication on the unit. Taking powers therefore gives
an isomorphism from each scalar cone to its tensor Koszul level. Naturality of the
tensor-cone comparison identifies the (scalar,identity) transition squares, and its
inclusion formula identifies the augmentations. Compare the products and their
one-minus-shift endomorphisms, then their mapping cocones. The normalized comparison
carries the zero-homotopy lift of the original augmentation to the tensor Koszul
Roos unit. All finite level comparisons are isomorphisms; neither regularity of the
scalar nor K-flatness or boundedness of P enters this calculation. -/
theorem principalConeKoszulRoosComparison
    (P : CochainComplex 𝒜 ℤ)
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (μ : End P)
    (hμ : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x =
        @SMul.smul _ _ ((P.X q).val.obj U).isModule.toSMul (a.val U) x) :
    ∃ e : (DerivedCategory.Q.{w} (C := 𝒜)).obj (CochainComplex.PrincipalCone.completion (A := 𝒜)
      (P := P) μ) ≅
        (DerivedCategory.Q.{w} (C := 𝒜)).obj
          ((roosF (A := 𝒜)).obj (koszulTowerComplex R (koszulTensorTower R P ⟨a.val, a.property⟩))),
      (DerivedCategory.Q.{w} (C := 𝒜)).map (CochainComplex.PrincipalCone.unit (A := 𝒜) (P := P) μ)
        ≫ e.hom =
        (DerivedCategory.Q.{w} (C := 𝒜)).map (principalKoszulRoosUnit R P ⟨a.val, a.property⟩) := by
  let b : (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections := ⟨a.val, a.property⟩
  set_option backward.isDefEq.respectTransparency false in
  have hm : μ = End.of (quotientAction R P b 0) := by
    apply End.ext
    ext q U x
    exact (hμ q U x).trans (by
      have h := (quotientAction_apply R P b 0 q U x).symm
      simp only [b, Nat.zero_add, pow_one] at h
      convert h using 1)
  subst μ
  obtain ⟨e, he⟩ := @coneTowerRoosComparison.{u, w} C inferInstance J R inferInstance P
    (End.of (quotientAction R P b 0)) (koszulTensorTower R P b)
    (koszulStrictAugmentation R P b)
    (fun n ↦ by
      simpa only [koszulTensorTower, Functor.comp_obj, principalKoszulTower,
        Functor.ofOpSequence_obj] using qConeIso R P b n)
    (fun n ↦ by
      simpa only [WeilConjectures.integralOperationsTowerStep, koszulTensorTower,
        Functor.comp_map, Functor.comp_obj, principalKoszulTower, Functor.ofOpSequence_obj,
        Functor.ofOpSequence_map_homOfLE_succ, id_eq]
        using qConeIso_step R P b n)
    (fun n ↦ by
      dsimp only [koszulStrictAugmentation, NatTrans.ofOpSequence]
      simpa only [
        quotientUnitIso_hom, koszulRepresentativeAugmentation, principalKoszulScalarComplex,
        koszulTensorTower,
        Functor.comp_obj, principalKoszulTower, Functor.ofOpSequence_obj, id_eq]
        using qConeIso_inr R P b n)
  exact ⟨e, by simpa only [principalKoszulRoosUnit, b] using he⟩

end CategoryTheory
