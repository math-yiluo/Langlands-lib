/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted

/-! # Compatible quotient augmentations before taking the Roos complex

Source: Stacks Project, Tags 03EK, 099N(5), and 08TC.
(blueprint: lem-zl-framework-quotient-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ZlFrameworkPbc
open PurCompactSupport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev quotientProjection (T : Scheme.{u}) (n : ℕ) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (completedIntegralCommRingProjectionUnrestricted l E T n)

private abbrev completedDirectMap {U T : Scheme.{u}} (h : U ⟶ T) :=
  (⟨Functor.whiskerRight
    (proEtaleRingDirectImageMap h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h)).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
    completedIntegralCoefficientSheafUnrestricted l E T ⟶
      ((proEtaleBaseChange h).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology T) (ProEt.topology U)).obj
          (completedIntegralCoefficientSheafUnrestricted l E U))

private theorem completedDirectMap_eq {U T : Scheme.{u}} (h : U ⟶ T) :
    proEtaleRingDirectImageMap h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h) = sfCompletedCoefficientMap l E h := by
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  change adj.unit.app _ ≫ (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
    ((adj.homEquiv _ _).symm _) = _
  exact (adj.homEquiv_unit _ _ _).symm.trans
    ((adj.homEquiv _ _).apply_symm_apply _)

private theorem quotientDirect_square {U T : Scheme.{u}} (h : U ⟶ T) (n : ℕ) :
    quotientProjection l E T n ≫ integralOperationsDirectRingMap l E h n =
      completedDirectMap l E h ≫
        ((proEtaleBaseChange h).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology T) (ProEt.topology U)).map (quotientProjection l E U n) := by
  have hh := (sfCompletedCoefficientMap_existsUnique l E h).exists.choose_spec n
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have hv := congrArg (fun a ↦ (forget₂ CommRingCat RingCat).map (a.hom.app V)) hh.symm
  dsimp only [completedDirectMap]
  rw [completedDirectMap_eq]
  exact hv

private abbrev quotientModuleMap {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) (i : ℤ) :=
  SheafOfModules.IntegralPullbackProof.mateData (proEtaleBaseChange h)
    (quotientProjection l E U n) (quotientProjection l E T n)
    (completedDirectMap l E h) (integralOperationsDirectRingMap l E h n)
    (quotientDirect_square l E h n)
    (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h))
    (integralOperationsPullbackAdjunction l E h n)
    ((unrestrictedTowerUnit l E T P n).f i)

private theorem quotientModuleMap_generator {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (n : ℕ) (i : ℤ) (V : T.ProEt) (x : (P.X i).val.obj (op V)) :
    (quotientModuleMap l E h P n i).val.app (op ((proEtaleBaseChange h).obj V))
      (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
        ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
          (op V) x) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E T n (P.X i) (op V) 1 x) := by
  have hh := SheafOfModules.IntegralPullbackProof.mateData_unit_formula
    (proEtaleBaseChange h) (quotientProjection l E U n) (quotientProjection l E T n)
    (completedDirectMap l E h) (integralOperationsDirectRingMap l E h n)
    (quotientDirect_square l E h n)
    (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull h))
    (integralOperationsPullbackAdjunction l E h n)
    ((unrestrictedTowerUnit l E T P n).f i) (op V) x
  change _ = integralOperationsPullbackGenerator l E h n _ V
    (((unrestrictedTowerUnit l E T P n).f i).val.app (op V) x) at hh
  rw [unrestrictedTowerUnit_condition] at hh
  exact hh

private def quotientChainMap {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    ((proEtaleRingModulePullback h ((completed l E).ring T)
      ((completed l E).ring U) ((completed l E).pull h)).mapHomologicalComplex
        (.up ℤ)).obj P ⟶ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n) where
  f i := quotientModuleMap l E h P n i
  comm' i j _ := by
    have hh := SheafOfModules.IntegralPullbackProof.mateData_naturality
      (proEtaleBaseChange h) (quotientProjection l E U n) (quotientProjection l E T n)
      (completedDirectMap l E h) (integralOperationsDirectRingMap l E h n)
      (quotientDirect_square l E h n)
      (proEtaleRingModuleAdjunction h ((completed l E).ring T) ((completed l E).ring U)
        ((completed l E).pull h))
      (integralOperationsPullbackAdjunction l E h n)
      ((unrestrictedTowerUnit l E T P n).f i) ((unrestrictedTowerUnit l E T P n).f j)
      (P.d i j) (((unrestrictedIntegralFiniteComplex l E T n).obj P).d i j)
      ((unrestrictedTowerUnit l E T P n).comm i j).symm
    exact hh.symm

private theorem quotientChainMap_transition {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    quotientChainMap l E h P (n + 1) ≫
      ((integralOperationsPullbackTowerFunctor l E h).obj P).map
        (homOfLE (Nat.le_succ n)).op = quotientChainMap l E h P n := by
  change quotientChainMap l E h P (n + 1) ≫
    ((Functor.ofOpSequence (integralOperationsPullbackTransition l E h)).map
      (homOfLE (Nat.le_succ n)).op).app P = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  ext i : 1
  apply ((proEtaleRingModuleAdjunction h ((completed l E).ring T)
    ((completed l E).ring U) ((completed l E).pull h)).homEquiv (P.X i) _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((integralOperationsPullbackTransition l E h n).app P).f i).val.app
    (op ((proEtaleBaseChange h).obj V.unop))
      ((quotientModuleMap l E h P (n + 1) i).val.app _
        (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
          ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app V x)) = _
  rw [quotientModuleMap_generator]
  have ht := (integralOperationsPullbackTransition_existsUnique l E h n).exists.choose_spec
    P i V.unop (unrestrictedIntegralTensorSection l E T (n + 1)
      (P.X i) V 1 x)
  refine ht.trans ?_
  have hh := (unrestrictedIntegralTransition_existsUnique l E T n).exists.choose_spec
    P i V 1 x
  rw [map_one] at hh
  have he := congrArg (integralOperationsPullbackGenerator l E h n
    (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V.unop) hh
  exact he.trans (quotientModuleMap_generator l E h P n i V.unop x).symm

/-- The finite quotient-unit maps commute with every consecutive quotient transition.
Source: Stacks Project, Tags 03EK and 099N(5), quotient-unit construction
(blueprint: lem-zl-framework-quotient-augmentation).

Proof: in degree i, compose the ordinary quotient unit x ↦ 1 tensor x with
inverse image. Identify the pulled quotient coefficients with the target quotient
coefficients using the constant-section coefficient comparison. Equivalently, take
its transpose under the completed module pullback/direct-image adjunction: it is
the finite pullback unit applied to the ordinary quotient unit. The coefficient
square with the completed projections makes this transpose linear over the
completed coefficient ring. The adjunction supplies the required module map.
Naturality of both units gives its chain condition. On inverse-image generators
its value is precisely the finite unit on 1 tensor x, as displayed below.
The quotient transition takes this generator to the next quotient generator,
since the quotient homomorphism takes 1 to 1. The defining transition equation
and uniqueness of adjuncts therefore give the consecutive compatibility equation.
This constructs one compatible family of chain maps, before any product or Roos
complex is formed. No completeness or flatness assumption is needed. -/
theorem frameworkQuotientAugmentation_exists {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    ∃ γ : ∀ n : ℕ,
      ((proEtaleRingModulePullback h ((completed l E).ring T)
        ((completed l E).ring U) ((completed l E).pull h)).mapHomologicalComplex
          (.up ℤ)).obj P ⟶ ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n),
      (∀ n : ℕ, γ (n + 1) ≫
        ((integralOperationsPullbackTowerFunctor l E h).obj P).map
          (homOfLE (Nat.le_succ n)).op = γ n) ∧
      (∀ (n : ℕ) (i : ℤ) (V : T.ProEt) (x : (P.X i).val.obj (op V)),
        ((γ n).f i).val.app (op ((proEtaleBaseChange h).obj V))
          (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
            ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
              (op V) x) =
          integralOperationsPullbackGenerator l E h n
            (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
            (unrestrictedIntegralTensorSection l E T n (P.X i) (op V) 1 x)) := by
  exact ⟨quotientChainMap l E h P, quotientChainMap_transition l E h P,
    quotientModuleMap_generator l E h P⟩

end WeilConjectures.ZlFrameworkPbc
