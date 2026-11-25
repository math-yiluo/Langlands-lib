/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparison
import WeilConjectures.CategoryTheory.ProductShift.ProductCommShift
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import all WeilConjectures.SmoothPurity.Completed.CompletedScalarShiftDescent

set_option linter.privateModule false

/-! # Signed shifts for integral pullback

Source: Stacks Project, Tags 011G, 014E, 06YS, 06YT and 0941.
(blueprint: lem-a1-integral-pullback-signed-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
private instance (priority := 6000) fixedSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _
namespace WeilConjectures.IntegralCompletedComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

private abbrev levelModules (n : ℕ) :=
  FinitePullbackStrictTower.finiteLevelModules.{u, u} l E g n

private abbrev level (n : ℕ) :
    CochainComplex (integralTowerModules.{u, u} l E Y) ℤ ⥤
      CochainComplex (integralTowerModules.{u, u} l E X) ℤ :=
  integralOperationsPullbackLevel.{u, u} l E g n

@[instance_reducible]
private def levelShiftData (n : ℕ) : (level l E g n).CommShift ℤ := by
  letI := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  letI := integralOperationsLevelPullback_additive.{u, u} l E g n
  let F := unrestrictedIntegralReductionFunctor.{u, u} l E Y n ⋙
    integralOperationsLevelPullback.{u, u} l E g n ⋙
    SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))
  exact inferInstanceAs ((F.mapHomologicalComplex (.up ℤ)).CommShift ℤ)

private instance level_commShift (n : ℕ) : (level l E g n).CommShift ℤ :=
  levelShiftData l E g n

private abbrev prodFunctor :
    CochainComplex (integralTowerModules.{u, u} l E Y) ℤ ⥤
      CochainComplex (integralTowerModules.{u, u} l E X) ℤ :=
  ProductShift.productFunctor (level l E g)

private instance prod_commShift : (prodFunctor l E g).CommShift ℤ :=
  ProductShift.productCommShift (level l E g)

private def transition : prodFunctor l E g ⟶ prodFunctor l E g where
  app := roosEnd l E g
  naturality P Q f := by
    change Limits.Pi.map
      (fun n ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).map f).app (op n)) ≫
        roosEnd l E g Q = _
    exact (integralOperationsRoos_square
      ((integralOperationsPullbackTowerFunctor.{u, u} l E g).map f)).symm

private theorem product_transition_shift
    {A D : Type*} [Category A] [Category D] [Preadditive D]
    [HasShift A ℤ] [HasShift D ℤ] [HasCountableProducts D]
    [∀ r : ℤ, (shiftFunctor D r).Additive]
    (F : ℕ → A ⥤ D) [∀ n, (F n).CommShift ℤ]
    (τ : ∀ n, F (n + 1) ⟶ F n)
    (hτ : ∀ n, NatTrans.CommShift (τ n) ℤ)
    (U : ProductShift.productFunctor F ⟶ ProductShift.productFunctor F)
    (hU : ∀ (P : A) (n : ℕ), U.app P ≫ Pi.π (fun k ↦ (F k).obj P) n =
      Pi.π (fun k ↦ (F k).obj P) n -
        Pi.π (fun k ↦ (F k).obj P) (n + 1) ≫ (τ n).app P) :
    letI := ProductShift.productCommShift F
    NatTrans.CommShift U ℤ := by
  let := ProductShift.productCommShift F
  let := hτ
  constructor
  intro r
  apply NatTrans.ext
  funext P
  change (ProductShift.productShiftIso F P r).hom ≫ (U.app P)⟦r⟧' =
    U.app (P⟦r⟧) ≫ (ProductShift.productShiftIso F P r).hom
  apply ProductShift.productShift_hom_ext F P r
  intro n
  rw [Category.assoc, ← Functor.map_comp, hU]
  rw [Category.assoc, ProductShift.productShiftIso_π]
  simp only [Functor.map_sub, Functor.map_comp, Preadditive.comp_sub]
  rw [ProductShift.productShiftIso_π, ProductShift.productShiftIso_π_assoc]
  conv_rhs => rw [← Category.assoc, hU]
  simp only [Preadditive.sub_comp, Category.assoc]
  rw [← NatTrans.shift_app_comm (τ n) r P]

private theorem transition_shift
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :
    NatTrans.CommShift (transition l E g) ℤ := by
  apply product_transition_shift (level l E g)
    (fun n ↦ integralOperationsPullbackTransition.{u, u} l E g n)
  · intro n
    constructor
    intro r
    apply NatTrans.ext
    funext P
    apply HomologicalComplex.hom_ext
    intro i
    have h := (((Functor.commShiftIso (FinitePullbackStrictTower.finiteComplex.{u, u} l E g)
      (self := C.finiteChainShift) r).hom.app P).f i).naturality
        (homOfLE (Nat.le_succ n)).op
    rw [C.finiteChainShift_normalization P r i n,
      C.finiteChainShift_normalization P r i (n + 1)] at h
    dsimp only [FinitePullbackStrictTower.finiteComplex, CompletedTowerIndependent.transpose,
      PrincipalQuotientCompletion.transpose, koszulTowerComplex, Functor.comp_obj] at h
    simp only [Functor.mapCochainComplexShiftIso_hom_app_f,
      CochainComplex.shiftFunctor_obj_X'] at h
    simp only [integralOperationsPullbackTowerFunctor, Functor.flip,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    change (((Functor.commShiftIso (level l E g (n + 1)) r).hom.app P).f i) ≫
        ((integralOperationsPullbackTransition.{u, u} l E g n).app P).f (i + r) =
      ((integralOperationsPullbackTransition.{u, u} l E g n).app (P⟦r⟧)).f i ≫
        (((Functor.commShiftIso (level l E g n) r).hom.app P).f i)
    change (𝟙 ((levelModules l E g (n + 1)).obj (P.X (i + r)))) ≫
        ((integralOperationsPullbackTransition.{u, u} l E g n).app P).f (i + r) =
      ((integralOperationsPullbackTransition.{u, u} l E g n).app (P⟦r⟧)).f i ≫
        𝟙 ((levelModules l E g n).obj (P.X (i + r)))
    exact h.symm
  · intro P n
    change roosEnd l E g P ≫
        Pi.π (fun k ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P).obj
          (op k)) n = _
    have h := (towerTransitionEndomorphism_eq_iff
      (K := fun n ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P).obj
        (op n))
      (integralOperationsTowerStep
        ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P)) _).mp rfl n
    change roosEnd l E g P ≫ _ = _ at h
    convert h using 1
    congr 2
    simp only [integralOperationsTowerStep, integralOperationsPullbackTowerFunctor,
      Functor.flip, Functor.ofOpSequence_map_homOfLE_succ]

@[instance_reducible]
private def chainShift
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :
    (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ :=
  by
  let := transition_shift l E g C
  exact SignedCoconeShift.coconeCommShift _ _ (transition l E g)

private theorem chainShift_coordinates
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g) :
    ShiftCoordinates l E g (chainShift l E g C) := by
  let := transition_shift l E g C
  intro P r
  constructor
  · intro j
    exact SignedCoconeShift.coconeFunctorShiftIso_inl _ _ (transition l E g) P r j
  · intro i j h
    exact SignedCoconeShift.coconeFunctorShiftIso_inr _ _ (transition l E g) P r i j h

end WeilConjectures.IntegralCompletedComparison
