/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

import WeilConjectures.Algebra.Homology.RoosCoordinatesQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

/-!
# Derived completion for pulled-back continuous integral coefficients

Source: blueprint main-20261015, chap-The-pro-etale-site,
`sk-def-pe-derived-completion/_section.md` (blueprint: definition-derived-adic-completeness).

The coefficient objects are the continuous condensed rings of DerivedNakayama,
pulled back by the published strong monoidal inverse image from the point.
Positive level n is indexed by n-1. Completion uses the explicit augmented Roos
complex on a K-flat representative, with zero homotopy in its second coordinate.
Normalization uses extension of scalars over the successive finite coefficient rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed modulesMonoidalPreadditive
  finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts complexNatLimit

private theorem restricted_linear {C : Type*} [Category C] [MonoidalCategory C]
    {R S T : C} [MonObj S] [MonObj T] (q : R ⟶ S) (r : R ⟶ T)
    (f : S ⟶ T) [IsMonHom f] (h : q ≫ f = r) :
    (q ▷ S ≫ μ[S]) ≫ f = R ◁ f ≫ (r ▷ T ≫ μ[T]) := by
  simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_def']
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, h]

private def genericRoosX {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (i : ℤ) := V.X i ⊞ V.X (i - 1)

private def genericRoosD {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    genericRoosX V i ⟶ genericRoosX V (i + 1) :=
  biprod.lift (biprod.fst ≫ V.d i (i + 1))
    (biprod.fst ≫ t.f i ≫
      eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ V.d (i - 1) ((i + 1) - 1))

private theorem genericRoosD_sq {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    genericRoosD V t i ≫ genericRoosD V t (i + 1) = 0 := by
  dsimp only [genericRoosD, genericRoosX]
  apply biprod.hom_ext
  · simp
  · suffices biprod.fst ≫ V.d i (i + 1 + 1 - 1) ≫ t.f (i + 1 + 1 - 1) -
        biprod.fst ≫ eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm) ≫
          V.d (i + 1 - 1) (i + 1 + 1 - 1) ≫ t.f (i + 1 + 1 - 1) = 0 by
      simpa using this
    have hd := V.eqToHom_comp_d
      (i := i) (i' := i + 1 - 1) (j := i + 1 + 1 - 1)
      (by change i + 1 = i + 1 + 1 - 1; omega)
      (by change i + 1 - 1 + 1 = i + 1 + 1 - 1; omega)
    rw [reassoc_of% hd, sub_self]

private def genericRoos {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) : CochainComplex C ℤ :=
  CochainComplex.of (genericRoosX V) (genericRoosD V t) (genericRoosD_sq V t)

private theorem quotientUnit_step (n : ℕ) :
    quotientUnit l E (n + 1) ≫ quotientStep l E n = quotientUnit l E n := by
  apply Mod.hom_ext
  rfl

private theorem finiteUnit_step (X : Scheme.{u}) (n : ℕ) :
    finiteUnit l E X (n + 1) ≫
      (DerivedNakayama.pullback l E X).map (quotientStep l E n) = finiteUnit l E X n := by
  dsimp only [finiteUnit]
  rw [Category.assoc, ← Functor.map_comp, quotientUnit_step]

private theorem levelUnit_step (X : Scheme.{u}) (P : CochainComplex (Modules l E X) ℤ)
    (n : ℕ) : levelUnit l E X P (n + 1) ≫ levelStep l E X P n = levelUnit l E X P n := by
  apply HomologicalComplex.hom_ext
  intro i
  change ((ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X (n + 1)) ≫
    P.X i ◁ (DerivedNakayama.pullback l E X).map (quotientStep l E n) =
    (ρ_ (P.X i)).inv ≫ P.X i ◁ finiteUnit l E X n
  rw [Category.assoc, ← whiskerLeft_comp, finiteUnit_step]

private theorem unitProduct_oneSubShift (X : Scheme.{u})
    (P : CochainComplex (Modules l E X) ℤ) :
    unitProduct l E X P ≫ oneSubShift l E X P = 0 := by
  apply Pi.hom_ext
  intro n
  simp [oneSubShift, towerTransitionEndomorphism, towerProductShift, unitProduct,
    levelUnit_step]

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts
  AdicCompletion.modulesNatProducts AdicCompletion.complexNatProducts
  AdicCompletion.complexNatLimit

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint
attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed
  modulesMonoidalPreadditive finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private def finiteModuleIso (X : Scheme.{u}) (n : ℕ) :
    finiteModule l E X n ≅ (Mod.comap (quotient l E X n)).obj
      (Mod.regular (finiteRing l E X n)) :=
  (Functor.mapModComapIso (upperStarFromPoint X)
    (DerivedNakayama.reductionRing l E (n + 1))).app
      (Mod.regular (DerivedNakayama.quotientRing l E (n + 1)))

private theorem genericCocone_d_snd {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (q : ℤ) :
    (CochainComplex.mappingCocone t).d q (q + 1) ≫
        (CochainComplex.mappingCocone.snd t).v
          (q + 1) q (by omega) =
      -((CochainComplex.mappingCocone.snd t).v
          q (q - 1) (by omega) ≫ V.d (q - 1) q) -
        (CochainComplex.mappingCocone.fst t).f q ≫
          t.f q := by
  have h := CochainComplex.mappingCone.d_snd_v t
    (q + -1) q (by omega)
  simp only [CochainComplex.mappingCocone.snd, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cocycle.leftShift_coe, HomologicalComplex.neg_f_apply,
    CochainComplex.HomComplex.Cocycle.homOf]
  rw [CochainComplex.HomComplex.Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ q (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 0) _ _ _ _ _ _ _ (q + -1) (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 1) _ _ _ _ _ _ _ (q + -1) (by omega)]
  dsimp only [CochainComplex.mappingCocone]
  simp only [show (-1 * -1 + -1 * (-1 - 1) / 2 : ℤ) = 2 by rfl,
    show (-1 * 0 + -1 * (-1 - 1) / 2 : ℤ) = 1 by rfl,
    show Int.negOnePow 2 = 1 by rfl, Int.negOnePow_one, Units.neg_smul,
    one_smul, neg_neg, CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg,
    CochainComplex.shiftFunctorObjXIso, Preadditive.neg_comp, Category.assoc,
    HomologicalComplex.d_comp_XIsoOfEq_hom_assoc]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  rw [← V.XIsoOfEq_hom_comp_d (by omega : q - 1 = q + -1) q]
  simp only [← Category.assoc, CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom]
  rw [h]
  erw [Category.id_comp, Category.id_comp]
  simp only [neg_add_rev]
  abel

private def genericCoconeCoordinateIso {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    (CochainComplex.mappingCocone t).X i ≅ (genericRoos V t).X i where
  hom := biprod.lift ((CochainComplex.mappingCocone.fst t).f i)
    (-(CochainComplex.mappingCocone.snd t).v i (i - 1) (by omega))
  inv := biprod.desc ((CochainComplex.mappingCocone.inl t).v i i
    (add_zero i))
    (-(CochainComplex.mappingCocone.inr t).1.v
      (i - 1) i (by omega))
  hom_inv_id := by
    simpa [biprod.lift_desc] using
      CochainComplex.mappingCocone.id_X t i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

private def genericCoconeIso {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) :
    CochainComplex.mappingCocone t ≅ genericRoos V t :=
  HomologicalComplex.Hom.isoOfComponents (genericCoconeCoordinateIso V t) (by
    intro q r h
    obtain rfl : q + 1 = r := h
    apply biprod.hom_ext
    · simp only [genericCoconeCoordinateIso, genericRoos, CochainComplex.of_d, genericRoosD,
        Category.assoc, biprod.lift_fst_assoc, biprod.lift_fst]
      exact (CochainComplex.mappingCocone.fst t).comm q (q + 1)
    · simp only [genericCoconeCoordinateIso, genericRoos, CochainComplex.of_d, genericRoosD,
        Category.assoc, Preadditive.comp_sub, biprod.lift_fst_assoc,
        biprod.lift_snd_assoc, biprod.lift_snd]
      have hq : q + 1 - 1 = q := by omega
      apply (cancel_mono (eqToHom (congrArg V.X hq))).mp
      simp only [Preadditive.sub_comp, Category.assoc, Preadditive.neg_comp,
        Preadditive.comp_neg, eqToHom_trans]
      rw [show V.d (q - 1) (q + 1 - 1) ≫
          eqToHom (congrArg V.X hq) =
          V.d (q - 1) q by
        exact V.d_comp_XIsoOfEq_hom hq (q - 1)]
      rw [show (CochainComplex.mappingCocone.snd t).v
          (q + 1) (q + 1 - 1) (by omega) ≫
          eqToHom (congrArg V.X hq) =
          (CochainComplex.mappingCocone.snd t).v
            (q + 1) q (by omega) by
        exact CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom _ _ _ _ _ hq]
      simp only [eqToHom_refl, Category.comp_id]
      rw [genericCocone_d_snd]
      simp [neg_sub, sub_neg_eq_add])

private theorem genericCoconeIso_inv_fst_f
    {C : Type v} [Category.{w} C] [Abelian C]
    (V : CochainComplex C ℤ) (t : V ⟶ V) (i : ℤ) :
    (genericCoconeIso V t).inv.f i ≫ (CochainComplex.mappingCocone.fst t).f i =
      (biprod.fst : (genericRoos V t).X i ⟶ V.X i) := by
  change (genericCoconeCoordinateIso V t i).inv ≫
    (CochainComplex.mappingCocone.fst t).f i = _
  apply (cancel_epi (genericCoconeCoordinateIso V t i).hom).mp
  rw [Iso.hom_inv_id_assoc]
  simp only [genericCoconeCoordinateIso, biprod.lift_fst]

private theorem modules_countableAB4Star : CountableAB4Star (Modules l E X) :=
  .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
    Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)

/-- The levelwise product map used by the recorded signed Roos chain map.
Source: the functorial reduction-tower construction
(blueprint: definition-derived-adic-completeness). -/
def productMap {P P' : CochainComplex (Modules l E X) ℤ} (a : P ⟶ P') :
    product l E X P ⟶ product l E X P' :=
  Limits.Pi.map (fun n ↦ (level l E X n).map a)

private theorem productMap_oneSubShift {P P' : CochainComplex (Modules l E X) ℤ}
    (a : P ⟶ P') :
    productMap l E X a ≫ oneSubShift l E X P' =
      oneSubShift l E X P ≫ productMap l E X a := by
  apply Pi.hom_ext
  intro n
  have ht := (NatTrans.mapHomologicalComplex
    ((tensoringRight (Modules l E X)).map
      ((DerivedNakayama.pullback l E X).map (quotientStep l E n))) (.up ℤ)).naturality a
  change (level l E X (n + 1)).map a ≫ levelStep l E X P' n =
    levelStep l E X P n ≫ (level l E X n).map a at ht
  simp [productMap, oneSubShift, towerTransitionEndomorphism, towerProductShift,
    Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp, ht]

private theorem genericRoosMap_comm
    {A : Type v} [Category.{w} A] [Abelian A]
    {V V' : CochainComplex A ℤ} (t : V ⟶ V) (t' : V' ⟶ V')
    (a : V ⟶ V') (h : a ≫ t' = t ≫ a) (i : ℤ) :
    biprod.map (a.f i) (a.f (i - 1)) ≫ genericRoosD V' t' i =
      genericRoosD V t i ≫ biprod.map (a.f (i + 1)) (a.f ((i + 1) - 1)) := by
  have hs (j : ℤ) := congrArg (fun f ↦ HomologicalComplex.Hom.f f j) h
  dsimp only [HomologicalComplex.comp_f] at hs
  apply biprod.hom_ext
  · simp +instances [genericRoosD, genericRoosX, Category.assoc]
  · simp +instances only [genericRoosX, genericRoosD, add_sub_cancel_right,
      eqToHom_naturality, Category.assoc, biprod.lift_snd, Preadditive.comp_sub,
      biprod.map_fst_assoc, eqToHom_naturality_assoc, biprod.map_snd_assoc,
      HomologicalComplex.Hom.comm, biprod.map_snd, biprod.lift_snd_assoc,
      Preadditive.sub_comp, sub_left_inj]
    rw [hs (i + 1 - 1)]

/-- The recorded coordinatewise product map commutes with the signed Roos differential.
Source: the functorial reduction-tower construction
(blueprint: definition-derived-adic-completeness).
Proof: productMap commutes with the one-minus-shift operator because the quotient
tensor transitions are natural. Apply the chain-map equations to the first coordinate
and this commutation equation to the second; both mixed differential terms agree. -/
theorem roosMap_comm {P P' : CochainComplex (Modules l E X) ℤ}
    (a : P ⟶ P') (i : ℤ) :
    biprod.map ((productMap l E X a).f i) ((productMap l E X a).f (i - 1)) ≫
        (roos l E X P').d i (i + 1) =
      (roos l E X P).d i (i + 1) ≫
        biprod.map ((productMap l E X a).f (i + 1))
          ((productMap l E X a).f ((i + 1) - 1)) := by
  simpa only [roos, CochainComplex.of_d, roosD, genericRoosD, genericRoosX, roosX]
    using genericRoosMap_comm (oneSubShift l E X P) (oneSubShift l E X P')
    (productMap l E X a) (productMap_oneSubShift l E X a) i

/-- The coordinatewise chain map of the recorded signed Roos model.
Source: functoriality of the derived-completeness construction
(blueprint: definition-derived-adic-completeness). -/
def roosMap {P P' : CochainComplex (Modules l E X) ℤ} (a : P ⟶ P') :
    roos l E X P ⟶ roos l E X P' :=
  CochainComplex.ofHom
    (fun i ↦ biprod.map ((productMap l E X a).f i) ((productMap l E X a).f (i - 1)))
    (roosMap_comm l E X a)

private theorem augmentation_naturality {P P' : CochainComplex (Modules l E X) ℤ}
    (a : P ⟶ P') :
    augmentation l E X P ≫ roosMap l E X a = a ≫ augmentation l E X P' := by
  ext i : 1
  change biprod.lift ((unitProduct l E X P).f i) 0 ≫
    biprod.map ((productMap l E X a).f i) ((productMap l E X a).f (i - 1)) =
      a.f i ≫ biprod.lift ((unitProduct l E X P').f i) 0
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    have h : unitProduct l E X P ≫ productMap l E X a = a ≫ unitProduct l E X P' := by
      apply Pi.hom_ext
      intro n
      simp only [unitProduct, productMap, Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc,
        Pi.lift_comp_π]
      exact ((NatTrans.mapHomologicalComplex
        ((rightUnitorNatIso (Modules l E X)).inv ≫
          (tensoringRight (Modules l E X)).map (finiteUnit l E X n)) (.up ℤ)).naturality a).symm
    exact congrArg (fun f ↦ f.f i) h
  · simp

private theorem roosMap_quasiIso
    {P P' : CochainComplex (Modules l E X) ℤ}
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P')
    (a : P ⟶ P') [QuasiIso a] : QuasiIso (roosMap l E X a) := by
  let := modules_countableAB4Star l E X
  have hlevel (n : ℕ) : QuasiIso ((level l E X n).map a) := by
    let F := tensorRight (finiteModule l E X n)
    let : F.PreservesKFlatQuasiIso :=
      Functor.PreservesKFlatQuasiIso.mk' F
        (fun K hK hKa ↦ CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa _)
    exact F.quasiIso_mapHomologicalComplex_map_of_kFlat hP hP' a
  let f := Discrete.natTrans
    (F := Discrete.functor (fun n : ℕ ↦ (level l E X n).obj P))
    (G := Discrete.functor (fun n : ℕ ↦ (level l E X n).obj P'))
    (fun n ↦ (level l E X n.as).map a)
  have (n : Discrete ℕ) : QuasiIso (f.app n) := hlevel n.as
  have hp : QuasiIso (productMap l E X a) := HomologicalComplex.quasiIso_limMap f
  exact CochainComplex.quasiIso_of_roos_coordinates
    (product l E X P) (product l E X P') (roos l E X P) (roos l E X P')
    (oneSubShift l E X P) (oneSubShift l E X P')
    (fun _ ↦ Iso.refl _) (fun _ ↦ Iso.refl _)
    (by intro i; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      roos, CochainComplex.of_d, roosD])
    (by intro i; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
      roos, CochainComplex.of_d, roosD])
    (productMap l E X a) (roosMap l E X a) (by intro i; rfl) hp

private theorem generic_augmentation_isIso_iff
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    (good : CochainComplex A ℤ → Prop)
    (hres : ∀ Z : CochainComplex A ℤ,
      ∃ (W : CochainComplex A ℤ) (q : W ⟶ Z), QuasiIso q ∧ good W)
    (T : CochainComplex A ℤ → CochainComplex A ℤ)
    (eta : ∀ P, P ⟶ T P)
    (mapT : ∀ {P P' : CochainComplex A ℤ}, (P ⟶ P') → (T P ⟶ T P'))
    (hnat : ∀ {P P' : CochainComplex A ℤ} (a : P ⟶ P'),
      eta P ≫ mapT a = a ≫ eta P')
    (hmap : ∀ {P P' : CochainComplex A ℤ}, good P → good P' →
      ∀ (a : P ⟶ P') [QuasiIso a], QuasiIso (mapT a))
    (P P' : CochainComplex A ℤ) (hP : good P) (hP' : good P')
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    IsIso (DerivedCategory.Q.map (eta P)) ↔ IsIso (DerivedCategory.Q.map (eta P')) := by
  classical
  obtain ⟨Z, t, ht, f, he⟩ := DerivedCategory.right_fac e.hom
  let := ht
  have ht' : QuasiIso t := (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 ht
  have hf : IsIso (DerivedCategory.Q.map f) := by
    have hh : DerivedCategory.Q.map f = DerivedCategory.Q.map t ≫ e.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [hh]
    infer_instance
  have hf' : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).1 hf
  obtain ⟨W, q, hq, hW⟩ := hres Z
  let := ht'
  let := hf'
  let := hq
  let u := q ≫ t
  let b := q ≫ f
  have : QuasiIso u := inferInstance
  have : QuasiIso b := inferInstance
  have := hmap hW hP u
  have := hmap hW hP' b
  have step (A : CochainComplex (A) ℤ)
      (c : W ⟶ A) [QuasiIso c] [QuasiIso (mapT c)] :
      IsIso (DerivedCategory.Q.map (eta W)) ↔
        IsIso (DerivedCategory.Q.map (eta A)) := by
    have hn := congrArg DerivedCategory.Q.map (hnat c)
    simp only [Functor.map_comp] at hn
    constructor
    · intro h
      let := h
      have : IsIso (DerivedCategory.Q.map c ≫
          DerivedCategory.Q.map (eta A)) := by rw [← hn]; infer_instance
      exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map c) _
    · intro h
      let := h
      have : IsIso (DerivedCategory.Q.map (eta W) ≫
          DerivedCategory.Q.map (mapT c)) := by rw [hn]; infer_instance
      exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map (mapT c))
  exact (step P u).symm.trans (step P' b)

private theorem augmentation_isIso_iff
    (P P' : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P')
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    IsIso (DerivedCategory.Q.map (augmentation l E X P)) ↔
      IsIso (DerivedCategory.Q.map (augmentation l E X P'))  := by
  exact generic_augmentation_isIso_iff
    ((HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat)
    (fun Z ↦ by
      obtain ⟨W, q, hq, _, hW⟩ := CochainComplex.exists_quasiIso_flat_kFlat Z
      exact ⟨W, q, hq, hW⟩)
    (roos l E X) (augmentation l E X) (roosMap l E X)
    (augmentation_naturality l E X) (roosMap_quasiIso l E X) P P' hP hP' e

end AlgebraicGeometry.ProEtale.AdicCompletion

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint
attribute [local instance] ringMonoidalObject ringCommutative finiteRingMonoidalObject
  finiteRingCommutative modulesMonoidal modulesSymmetric modulesClosed
  modulesMonoidalPreadditive finiteModulesDerived modulesDerived modulesProducts complexProducts
  modulesNatProducts complexNatProducts complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The full inverse-system functor of canonical derived reductions.
Source: blueprint, derived inverse limit (blueprint: definition-derived-adic-completeness). -/
def derivedTower (K : DerivedCategory (Modules l E X)) :
    ℕᵒᵖ ⥤ DerivedCategory (Modules l E X) :=
  Functor.ofOpSequence (integralStep l E X K)

private theorem strictScalarRealization
    (K : DerivedCategory (Modules l E X)) (P : CochainComplex (Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)).kFlat P)
    (eP : DerivedCategory.Q.obj P ≅ K) :
    ∃ e : ∀ n, DerivedCategory.Q.obj ((level l E X n).obj P) ≅ integralLevel l E X K n,
      (∀ n, DerivedCategory.Q.map (levelStep l E X P n) ≫ (e n).hom =
        (e (n + 1)).hom ≫ integralStep l E X K n) ∧
      (∀ n, DerivedCategory.Q.map (levelUnit l E X P n) ≫ (e n).hom =
        eP.hom ≫ (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app K)
    := by
  exact Mod.KFlatScalarTower.realization
    (ring l E X) (finiteRing l E X) (quotient l E X) (transition l E X)
    (quotient_transition l E X) (finiteModule l E X) (finiteUnit l E X)
    (fun n ↦ (DerivedNakayama.pullback l E X).map (quotientStep l E n))
    (finiteModuleIso l E X)
    (by
      intro n
      change (𝟙 _ ≫ (upperStarFromPoint X).map
        (DerivedNakayama.reductionRing l E (n + 1))) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id])
    (by
      intro n
      change (upperStarFromPoint X).map (transitionRing l E n) ≫ 𝟙 _ =
        𝟙 _ ≫ (upperStarFromPoint X).map (transitionRing l E n)
      simp only [Category.id_comp, Category.comp_id]) K P hP eP

private theorem composed_unit_compatible
    {C D A : Type*} [Category C] [Category D] [Category A]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ A} {I : A ⥤ D}
    {L : C ⥤ A} {R : A ⥤ C}
    (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ R) (e : I ⋙ G ≅ R) (K : C) :
    let t := ((a.comp b).ofNatIsoRight e).leftAdjointUniq c
    a.unit.app K ≫ (G.map (b.unit.app (F.obj K) ≫ I.map (t.hom.app K)) ≫
      e.hom.app (L.obj K)) = c.unit.app K := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app ((a.comp b).ofNatIsoRight e) c K
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, Category.assoc, Functor.whiskerLeft_app] at h
  rw [← e.hom.naturality ((((a.comp b).ofNatIsoRight e).leftAdjointUniq c).hom.app K)] at h
  simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using h


private theorem generic_roosLimit
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    [HasCountableProducts A] [CountableAB4Star A]
    (V : ℕ → CochainComplex A ℤ) (t : ∀ n, V (n + 1) ⟶ V n)
    (P : CochainComplex A ℤ) (K : DerivedCategory A)
    (e : DerivedCategory.Q.obj P ≅ K)
    (D : ℕ → DerivedCategory A) (d : ∀ n, D (n + 1) ⟶ D n) [HasProduct D]
    (c : ∀ n, P ⟶ V n) (uD : ∀ n, K ⟶ D n)
    (aug : P ⟶ genericRoos (∏ᶜ V) (towerTransitionEndomorphism t))
    (haug : aug ≫ (genericCoconeIso (∏ᶜ V) (towerTransitionEndomorphism t)).inv ≫
      CochainComplex.mappingCocone.fst (towerTransitionEndomorphism t) = Pi.lift c)
    (eL : ∀ n, DerivedCategory.Q.obj (V n) ≅ D n)
    (hstep : ∀ n, DerivedCategory.Q.map (t n) ≫ (eL n).hom = (eL (n + 1)).hom ≫ d n)
    (hunit : ∀ n, DerivedCategory.Q.map (c n) ≫ (eL n).hom = e.hom ≫ uD n) :
    ∃ (p : DerivedCategory.Q.obj
        (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)) ⟶ ∏ᶜ D)
      (δ : ∏ᶜ D ⟶ (DerivedCategory.Q.obj
        (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)))⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle d _ p δ ∧
        (e.inv ≫ DerivedCategory.Q.map aug) ≫ p = Pi.lift uD := by
  classical
  let Q := DerivedCategory.Q (C := A)
  have hp := (derivedCategory_termwiseProduct_isLimit A ℕ V).some
  let hfan := (Fan.isLimitMapConeEquiv Q V (limit.cone (Discrete.functor V))) hp
  let cone : Fan D := Fan.mk (Q.obj (∏ᶜ V))
    (fun n ↦ Q.map (Pi.π V n) ≫ (eL n).hom)
  let en : Discrete.functor (fun n ↦ Q.obj (V n)) ≅ Discrete.functor D :=
    Discrete.natIso (fun n ↦ eL n.as)
  let hc : IsLimit cone := (IsLimit.postcomposeHomEquiv en _).symm hfan
  let ep : Q.obj (∏ᶜ V) ≅ ∏ᶜ D :=
    hc.conePointUniqueUpToIso (productIsProduct D)
  have he (n : ℕ) : ep.hom ≫ Pi.π D n = Q.map (Pi.π V n) ≫ (eL n).hom :=
    hc.conePointUniqueUpToIso_hom_comp (productIsProduct D) ⟨n⟩
  have hs : Q.map (towerTransitionEndomorphism t) ≫ ep.hom =
      ep.hom ≫ towerTransitionEndomorphism d := by
    apply Pi.hom_ext
    intro n
    have hπ := (towerTransitionEndomorphism_eq_iff
      t (towerTransitionEndomorphism t)).mp rfl n
    have hdπ := (towerTransitionEndomorphism_eq_iff
      d (towerTransitionEndomorphism d)).mp rfl n
    simp only [Category.assoc, hdπ, Preadditive.comp_sub, he]
    rw [← Q.map_comp_assoc, hπ]
    simp only [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp]
    simp only [← Category.assoc, he]
    dsimp only [Q]
    simp only [Category.assoc, hstep]
  let ec := Q.mapIso (genericCoconeIso (∏ᶜ V) (towerTransitionEndomorphism t))
  let T := Q.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle (towerTransitionEndomorphism t))
  let p : Q.obj (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)) ⟶ ∏ᶜ D :=
    ec.inv ≫ T.mor₁ ≫ ep.hom
  let δ : ∏ᶜ D ⟶ (Q.obj (genericRoos (∏ᶜ V) (towerTransitionEndomorphism t)))⟦(1 : ℤ)⟧ :=
    ep.inv ≫ T.mor₃ ≫ ec.hom⟦(1 : ℤ)⟧'
  refine ⟨p, δ, ?_, ?_⟩
  · have hT : T ∈ distTriang (DerivedCategory A) :=
      DerivedCategory.mappingCocone_triangle_distinguished _
    exact (Pretriangulated.distinguished_iff_of_iso
      (Pretriangulated.Triangle.isoMk T
        (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism d) δ)
        ec ep ep (by simp [p]) hs (by simp [δ]))).mp hT
  · apply Pi.hom_ext
    intro n
    simp only [p, Category.assoc, he, ec, Functor.mapIso_inv]
    change e.inv ≫ Q.map aug ≫
      Q.map (genericCoconeIso (∏ᶜ V) (towerTransitionEndomorphism t)).inv ≫
      Q.map (CochainComplex.mappingCocone.fst (towerTransitionEndomorphism t)) ≫
      Q.map (Pi.π V n) ≫ (eL n).hom = _
    rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc aug, haug,
      ← Q.map_comp_assoc]
    simp only [Pi.lift_comp_π]
    rw [hunit, Iso.inv_hom_id_assoc]


end AlgebraicGeometry.ProEtale.AdicCompletion
