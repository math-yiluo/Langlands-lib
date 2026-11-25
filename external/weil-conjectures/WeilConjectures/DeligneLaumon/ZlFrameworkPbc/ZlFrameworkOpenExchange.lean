/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlCompactificationOpenDiagram
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.FourierTransform.FdPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProetaleStrictTowerRealization
import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlFrameworkQuotientAugmentation
import WeilConjectures.AlgebraicGeometry.Integral.IntegralRingedOpenPullSupport
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation

/-! # Framework open exchange in its own coefficient presentation
Source: thm-cbc-qbar.proof.md, integral strict quotient construction
(blueprint: def-zl-framework-open-exchange).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ZlFrameworkPbc

-- `SignedDoubleHomCone.moduleBinaryBiproducts` leaves its universe free and gets stuck
-- against the biproducts of the completed integral sheaf modules.
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts

open PurCompactSupport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary pullback with the framework completed coefficient sheaf.
Source: Stacks 099N(5) (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkModulePull {U T : Scheme.{u}} (h : U ⟶ T) :=
  proEtaleRingModulePullback h ((completed l E).ring T)
    ((completed l E).ring U) ((completed l E).pull h)

/-- The canonical quotient-unit/Roos normalization. It specifies every first-coordinate
projection on inverse-image generators and the entire shifted coordinate as zero.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange). -/
def FrameworkPullChainSpec {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P) : Prop :=
  (∀ (n : ℕ) (i : ℤ) (V : T.ProEt) (x : (P.X i).val.obj (op V)),
    ((ξ ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) ≫
      Pi.π (fun n ↦
        ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)) n).f i).val.app
        (op ((proEtaleBaseChange h).obj V))
      (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
        ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
          (op V) x) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E T n (P.X i) (op V) 1 x)) ∧
  (∀ (i j : ℤ) (hij : i + -1 = j), ξ.f i ≫
    (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P))).v
        i j hij = 0)

private theorem coconeDegree_ext
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {P K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (f g : P ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i)
    (hs : f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) :
    f.f i = g.f i := by
  have hi := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ _ := congrArg (f.f i ≫ ·) hi.symm
    _ = g.f i ≫ _ := by
      rw [Preadditive.comp_add, Preadditive.comp_add, reassoc_of% hf, reassoc_of% hs]
    _ = g.f i := by rw [hi, Category.comp_id]

private theorem frameworkPullChain_ext {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (ξ η : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P)
    (hξ : FrameworkPullChainSpec l E h P ξ)
    (hη : FrameworkPullChainSpec l E h P η) : ξ = η := by
  have hf : ξ ≫ CochainComplex.mappingCocone.fst
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) =
      η ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) := by
    apply Pi.hom_ext
    intro n
    ext i : 1
    apply ((proEtaleRingModuleAdjunction h ((completed l E).ring T)
      ((completed l E).ring U) ((completed l E).pull h)).homEquiv (P.X i) _).injective
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hξ.1 n i V.unop x).trans (hη.1 n i V.unop x).symm
  ext i : 1
  have hfi := congrArg (fun z ↦ z.f i) hf
  have hs := (hξ.2 i (i - 1) (by omega)).trans (hη.2 i (i - 1) (by omega)).symm
  exact coconeDegree_ext _ ξ η i hfi hs

/-- The quotient-unit comparison is uniquely determined before localization.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange).
Proof: apply inverse image to the quotient augmentation x maps to 1 tensor x at
all levels simultaneously. These maps commute with quotient transitions, so the
first-coordinate product map and zero shifted coordinate form a chain map to Roos.
The inverse-image generators generate after sheafification. Product projections
and the two cocone coordinates therefore determine the chain map uniquely. -/
theorem frameworkPullChain_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    ∃! ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P,
      FrameworkPullChainSpec l E h P ξ := by
  obtain ⟨γ, hγ, hgen⟩ := frameworkQuotientAugmentation_exists l E h P
  let C := (integralOperationsPullbackTowerFunctor l E h).obj P
  let α : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ∏ᶜ fun n : ℕ ↦ C.obj (op n) := Pi.lift γ
  have hα : α ≫ scalarRoosBoundary C = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [α, scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Category.comp_id, Category.assoc, Pi.lift_comp_π,
      Preadditive.sub_comp, zero_comp]
    rw [← Category.assoc, Pi.lift_comp_π]
    exact sub_eq_zero.mpr (hγ n).symm
  let ξ := CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 (by simp [hα])
  have hξ : FrameworkPullChainSpec l E h P ξ := by
    constructor
    · intro n i V x
      have hf : ξ ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
          Pi.π (fun n : ℕ ↦ C.obj (op n)) n = γ n := by
        rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst, Pi.lift_comp_π]
      exact (congrArg (fun f ↦ (f.f i).val.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
          ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
            (op V) x)) hf).trans (hgen n i V x)
    · intro i j hij
      exact CochainComplex.mappingCocone.lift_f_snd_v (scalarRoosBoundary C) α 0
        (by simp [hα]) i j hij
  exact ⟨ξ, hξ, fun η hη ↦ frameworkPullChain_ext l E h P η ξ hη hξ⟩

/-- The specified whole quotient-diagram augmentation into its Roos realization.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange). -/
def frameworkPullChain {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :=
  (frameworkPullChain_existsUnique l E h P).exists.choose

/-- Open inverse image preserves the completed constructible realization, with the
whole quotient-unit normalization. No PBC presentation or comparison enters this type.
Source: Stacks 099N(5), 09BQ (blueprint: def-zl-framework-open-exchange).
Proof: open inverse image is exact and preserves products. Apply it to the strict
quotient diagram of a flat K-flat representative. The quotient-unit map just
constructed becomes its canonical completion augmentation. Complete constructible
inputs have invertible augmentation; the Roos product and shifted coordinates
identify it with the defining integral pullback realization. Descent from good
representatives supplies naturality and uniqueness with this equation. -/
theorem frameworkOpenPullRealization_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :
    ∃! a : (sfIntegralConstructible l E T).ι ⋙ pull (completed l E) h ≅
      constructibleIntegralPullback l E h ⋙ (sfIntegralConstructible l E U).ι,
      ∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (hP : sfIntegralConstructible l E T (DerivedCategory.Q.obj P.obj)),
        a.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
          (integralDerivedPullbackComparison l E h).hom.app P =
        (frameworkModulePull l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (frameworkPullChain l E h P.obj) := by
  sorry

/-- The framework pullback realization fixed by quotient and shifted Roos coordinates.
Source: Stacks 099N(5) (blueprint: def-zl-framework-open-exchange). -/
def frameworkOpenPullRealization {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :=
  (frameworkOpenPullRealization_existsUnique l E h).exists.choose

end WeilConjectures.ZlFrameworkPbc
