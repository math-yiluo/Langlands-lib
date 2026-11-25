/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDerivedLimitFunctor
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # The normalized augmentation of the completed reduction tower

The module-level quotient units descend through the universal left-derived counit.
These constructions precede pullback and the comparison with Koszul completion.
Source: blueprint order 1261 (blueprint: def-weil-pbc-reduction-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The strict quotient-unit map is fixed on sections by x ↦ 1 tensor x.
Source: blueprint order 1261 (blueprint: def-weil-pbc-reduction-augmentation).
Proof: this formula is linear over the completed coefficient ring, commutes with
restriction, and is natural in the module. Each quotient transition takes 1 tensor x
to 1 tensor x, so the maps form a strict tower map. The sectionwise formula gives uniqueness. -/
theorem completedReductionModuleUnit_exists (T : Scheme.{u}) :
    ∃! τ : completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d,
      ∀ (M : pbcModules T (pbcAdicCompletion T d)) (n : ℕ)
        (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        ((τ.app M).app (op n)).val.app U x =
          reductionTensorSection T (pbcAdicProjection T d n) M U 1 x := by
  let u (M : pbcModules T (pbcAdicCompletion T d)) (n : ℕ) :
      M ⟶ (completedReductionLevel T d n).obj M :=
    (pbcScalarAdjunction (pbcAdicProjection T d n)).unit.app M
  have hu (M : pbcModules T (pbcAdicCompletion T d)) (n : ℕ)
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (u M n).val.app U x =
        reductionTensorSection T (pbcAdicProjection T d n) M U 1 x :=
    (pbcScalarAdjunction_exists (pbcAdicProjection T d n)).exists.choose_spec M U x
  let τ : completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d :=
    { app := fun M ↦ NatTrans.ofOpSequence (u M) (by
        intro n
        change u M n = u M (n + 1) ≫
          (completedReductionModuleTower T d M).map
            (homOfLE (n.le_add_right 1)).op
        dsimp only [completedReductionModuleTower]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        ext U x
        change (u M n).val.app U x =
          ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M).val.app U
            ((u M (n + 1)).val.app U x)
        rw [hu, hu]
        have ht := (completedReductionTransition_exists T d (n + 1) n
          (Nat.le_succ n)).exists.choose_spec M U 1 x
        dsimp only [completedReductionTransition] at *
        simpa only [map_one, pbcAdicProjection, completedReductionProjection,
          pbcAdicRings, reductionCoefficientSystem] using ht.symm)
      naturality := by
        intro M N a
        apply NatTrans.ext
        funext n
        exact (pbcScalarAdjunction (pbcAdicProjection T d n.unop)).unit.naturality a }
  refine ⟨τ, hu, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  exact (hτ' M n.unop U x).trans (hu M n.unop U x).symm

/-- The actual module-to-strict-tower quotient unit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-reduction-augmentation). -/
def completedReductionModuleUnit (T : Scheme.{u}) :
    completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d :=
  (completedReductionModuleUnit_exists d T).exists.choose

/-- The reduction tower's fixed universal counit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-reduction-augmentation). -/
def completedReductionTowerCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ completedReductionTower T d ⟶ completedReductionHomotopyFunctor T d :=
  (completedReductionTower_exists T d).choose_spec.choose

/-- The representative normalization fixing the canonical comparison uniquely.
Source: blueprint order 1261 (blueprint: def-weil-pbc-reduction-augmentation). -/
def HasCompletedReductionTowerUnitNormalization (T : Scheme.{u})
    (τ : completedDerivedConstant d T ⟶ completedReductionTower T d) : Prop :=
  letI := completedReductionModuleTowerFunctor_additive T d
  ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion T d) P →
        τ.app (DerivedCategory.Q.obj P) ≫
            (completedReductionTower T d).map
              ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
            (completedReductionTowerCounit d T).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
            DerivedCategory.Qh.map
              (((completedReductionModuleTowerFunctor T d).mapHomotopyCategoryFactors
                (.up ℤ)).hom.app P) ≫
            (DerivedCategory.quotientCompQhIso _).hom.app
              (((completedReductionModuleTowerFunctor T d).mapHomologicalComplex
                (.up ℤ)).obj P) =
          ((completedTowerConstant d T).mapDerivedCategoryFactors).hom.app P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T)
                (.up ℤ)).app P)

private theorem exactAugmentation_existsUnique
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (E F : B ⥤ C) [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))]
    (u : E ⟶ F) (S : CochainComplex B ℤ → Prop)
    (hiso : ∀ P, S P → IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)))
    (hrep : ∀ K : DerivedCategory B, ∃ P, S P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K)) :
    ∃! τ : E.mapDerivedCategory ⟶ L, ∀ P : CochainComplex B ℤ, S P →
      τ.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) =
        E.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) := by
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let β : DerivedCategory.Qh ⋙ E.mapDerivedCategory ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    E.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (NatTrans.mapHomotopyCategory u (.up ℤ)) DerivedCategory.Qh
  let τ := L.leftDerivedLift ε W E.mapDerivedCategory β
  have hτ (P : CochainComplex B ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) =
        E.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) := by
    have h := L.leftDerived_fac_app ε W E.mapDerivedCategory β
      ((HomotopyCategory.quotient B (.up ℤ)).obj P)
    change τ.app _ ≫ ε.app _ = E.mapDerivedCategoryFactorsh.hom.app _ ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory u (.up ℤ)).app _) at h
    rw [E.mapDerivedCategoryFactorsh_hom_app] at h
    change τ.app (DerivedCategory.Q.obj P) ≫
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) =
      (E.mapDerivedCategory.map (𝟙 _) ≫ E.mapDerivedCategoryFactors.hom.app P ≫
        𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) at h
    erw [E.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
      Category.id_comp, Category.comp_id, Category.comp_id] at h
    exact h
  refine ⟨τ, fun P _ ↦ hτ P, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext K
  obtain ⟨P, hP, ⟨e⟩⟩ := hrep K
  have := hiso P hP
  have he : τ'.app (DerivedCategory.Q.obj P) = τ.app (DerivedCategory.Q.obj P) := by
    apply (cancel_mono (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P))).1
    exact (hτ' P hP).trans (hτ P).symm
  apply (cancel_epi (E.mapDerivedCategory.map e.hom)).1
  rw [τ'.naturality, τ.naturality, he]

private theorem independentKFlatRepresentatives
    {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u₂} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u₂} RingCat.{u₂})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u₂}]
    [HasSheafify J AddCommGrpCat.{u₂}]
    (R : Sheaf J CommRingCat.{u₂})
    [HasDerivedCategory (SheafOfModules.{u₂}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (K : DerivedCategory (SheafOfModules.{u₂}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let G := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
  have := hp
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩

/-- The quotient unit descends uniquely from its strict K-flat construction.
Source: blueprint order 1261 (blueprint: def-weil-pbc-reduction-augmentation).
Proof: for a K-flat representative use its strict quotient-unit map, transported by
the invertible reduction counit. K-flat resolutions compare any two representatives;
naturality on this resolving class descends to the derived category. Every object has
such a representative, so the specified normalization determines the unit uniquely. -/
theorem completedReductionTowerUnit_exists (T : Scheme.{u}) :
    ∃! τ : completedDerivedConstant d T ⟶ completedReductionTower T d,
      HasCompletedReductionTowerUnitNormalization d T τ := by
  have : DerivedCategory.Qh.IsLocalization
      (HomotopyCategory.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ)) :=
    inferInstance
  have : (completedReductionTower T d).IsLeftDerivedFunctor
      (completedReductionTowerCounit d T)
      (HomotopyCategory.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ)) :=
    (completedReductionTower_properties T d).1
  have : (completedReductionModuleTowerFunctor T d).Additive :=
    completedReductionModuleTowerFunctor_additive T d
  have hrep := independentKFlatRepresentatives (pbcAdicCompletion T d)
  obtain ⟨τ, hτ, huniq⟩ := exactAugmentation_existsUnique (completedTowerConstant d T)
    (completedReductionModuleTowerFunctor T d) (completedReductionTower T d)
    (completedReductionTowerCounit d T) (completedReductionModuleUnit d T)
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) P)
    (completedReductionTower_properties T d).2.2 hrep
  refine ⟨τ, ?_, ?_⟩
  · intro P hP
    dsimp only [HasCompletedReductionTowerUnitNormalization, DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
      Functor.mapHomotopyCategoryFactors, NatIso.ofComponents, Iso.refl]
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact hτ P hP
  · intro τ' hτ'
    apply huniq τ'
    intro P hP
    have h := hτ' P hP
    dsimp only [HasCompletedReductionTowerUnitNormalization, DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift,
      Functor.mapHomotopyCategoryFactors, NatIso.ofComponents, Iso.refl] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h

/-- The canonical strict derived reduction unit ΔK → K_bullet.
Source: blueprint order 1261 (blueprint: def-weil-pbc-reduction-augmentation). -/
def completedReductionTowerUnit (T : Scheme.{u}) :
    completedDerivedConstant d T ⟶ completedReductionTower T d :=
  (completedReductionTowerUnit_exists d T).exists.choose

end AlgebraicGeometry.Scheme
