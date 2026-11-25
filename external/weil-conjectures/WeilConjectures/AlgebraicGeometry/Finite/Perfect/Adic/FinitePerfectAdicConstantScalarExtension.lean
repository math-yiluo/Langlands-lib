/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import all WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Scalar extension of small algebraic constant complexes

Source: Stacks Project, Tags 093J, 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local instance] ULift.algebra'

attribute [local irreducible] completedAdicChangeData completedAdicDerivedChange
  Functor.mapDerivedCategory HasDerivedCategory.standard Functor.leftAdjoint

private abbrev coefficientLift (A : Type t) [CommRing A] :
    ModuleCat.{t} A ⥤ ModuleCat.{t + 1} (ULift.{t + 1} A) :=
  ModuleCat.uliftFunctor.{t + 1, t} A ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom

private def liftedTensorIso {A B : Type t} [CommRing A] [CommRing B]
    (q : A →+* B) (M : ModuleCat.{t} A) :
    (coefficientLift B).obj ((ModuleCat.extendScalars q).obj M) ≅
      (ModuleCat.extendScalars (RingHom.ulift.{t + 1, t + 1} q)).obj
        ((coefficientLift A).obj M) := by
  letI := q.toAlgebra
  exact (show ULift.{t + 1} (B ⊗[A] M) ≃ₗ[ULift.{t + 1} B]
      (ULift.{t + 1} B ⊗[ULift.{t + 1} A] ULift.{t + 1} M) from
    { (TensorProduct.AlgebraTensorModule.uliftEquiv A B B M).toAddEquiv with
      map_smul' := fun b x ↦
        (TensorProduct.AlgebraTensorModule.uliftEquiv A B B M).map_smul b.down x
    }).toModuleIso

private def liftedTensorComparison {A B : Type t} [CommRing A] [CommRing B]
    (q : A →+* B) :
    ModuleCat.extendScalars q ⋙ coefficientLift B ≅
      coefficientLift A ⋙ ModuleCat.extendScalars (RingHom.ulift.{t + 1, t + 1} q) := by
  letI := q.toAlgebra
  refine NatIso.ofComponents (liftedTensorIso q) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨x⟩
  induction x using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy =>
    have h : (ULift.up (x + y) : ULift.{t + 1} _) = ULift.up x + ULift.up y := rfl
    simpa only [h, map_add] using congrArg₂ (· + ·) hx hy

private def constantFactorization (X : Scheme.{t}) (A : Type t) [CommRing A] :
    finitePerfectAdicDerivedConstant X A ≅
      (coefficientLift A).mapDerivedCategory ⋙
        commutativeSiteDerivedConstantModuleFunctor (ProEt.topology X) (ULift.{t + 1} A) := by
  have h := commutativeSiteConstantModuleFunctor_exact
    (ProEt.topology X) (ULift.{t + 1} A)
  have h' : (koszulConstantFunctor X A).Additive ∧
      PreservesFiniteLimits (koszulConstantFunctor X A) ∧
      PreservesFiniteColimits (koszulConstantFunctor X A) := h
  have := h'.1
  have := h'.2.1
  have := h'.2.2
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  exact Functor.mapDerivedCategoryNatIso
    (Functor.associator (ModuleCat.uliftFunctor.{t + 1, t} A)
      (ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom)
      (koszulConstantFunctor X A)).symm ≪≫
    (Functor.mapDerivedCategoryCompIso (coefficientLift A) (koszulConstantFunctor X A)).symm

/-- Constant realization, including its coefficient-universe lift, commutes with
algebraic derived scalar extension on a perfect complex.

Source: Stacks Project, Modules on Sites, Tag 093J; Cohomology on Sites,
Tags 06YY and 0D6D.
(blueprint: lem-weil-pbc-finite-perfect-adic-constant-scalar-extension).

Proof: represent P by a bounded complex of finite projective A-modules. Such a
complex is K-flat, and its termwise scalar extension computes algebraic derived
extension along q. Universe lift preserves its finite-projective splittings, so
its lifted complex is still bounded projective and K-flat. Apply the constant
realization tensor comparison to these lifted complexes. On ordinary tensor
products the comparison identifies a constant b tensor a lifted m with the lift
of b tensor m; the inverse follows from the tensor universal property. These
maps preserve the B-action, commute with differentials, and are natural in module
maps. The K-flat representative counits identify their localization with the two
derived functors in the conclusion. Transport along the chosen perfect model
isomorphism. No adic datum, completion, chart, or nonemptiness is used; the zero
ring and zero complex are included. -/
theorem finitePerfectAdicConstant_scalarExtension
    (X : Scheme.{t}) {A B : Type t} [CommRing A] [CommRing B] (q : A →+* B)
    (P : DerivedCategory (ModuleCat.{t} A)) (hP : DerivedCategory.IsPerfect P) :
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X q)).obj
          ((finitePerfectAdicDerivedConstant X A).obj P) ≅
        (finitePerfectAdicDerivedConstant X B).obj
          ((ConstantScalarRealization.moduleDerivedExtension q).obj P)) := by
  classical
  obtain ⟨K, a, b, ha, hb, hK, ⟨e⟩⟩ := hP
  let := hb
  let J := ProEt.topology X
  let q' := RingHom.ulift.{t + 1, t + 1} q
  let LA := coefficientLift A
  let LB := coefficientLift B
  let cB := commutativeSiteDerivedConstantModuleFunctor J (ULift.{t + 1} B)
  let D := completedAdicDerivedChange X (adicConstantMap X q)
  let K' : CochainComplex (ModuleCat.{t + 1} (ULift.{t + 1} A)) ℤ :=
    (LA.mapHomologicalComplex (.up ℤ)).obj K
  let Kq := ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj K
  have hk : K.IsKFlatForTotalTensor :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat K b (fun i ↦ by
      have := (hK i).1
      exact (ModuleCat.flat_iff_flat _).2 inferInstance)
  have hk' : K'.IsKFlatForTotalTensor :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat K' b (fun i ↦ by
      have := (hK i).1
      have : Module.Flat A (ULift.{t + 1} (K.X i)) := inferInstance
      have hf : Module.Flat (ULift.{t + 1} A) (ULift.{t + 1} (K.X i)) :=
        Module.Flat.ulift_left_iff.mpr this
      exact (ModuleCat.flat_iff_flat _).2 hf)
  have : IsIso (ConstantScalarRealization.moduleRepresentative q K) :=
    ConstantScalarRealization.moduleRepresentative_isIso q K hk
  have : IsIso (ConstantScalarRealization.moduleRepresentative q' K') :=
    ConstantScalarRealization.moduleRepresentative_isIso q' K' hk'
  let r : (ConstantScalarRealization.moduleDerivedExtension q).obj
      (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj Kq :=
    asIso (ConstantScalarRealization.moduleRepresentative q K)
  let r' : (ConstantScalarRealization.moduleDerivedExtension q').obj
      (LA.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      LB.mapDerivedCategory.obj
        ((ConstantScalarRealization.moduleDerivedExtension q).obj (DerivedCategory.Q.obj K)) :=
    (ConstantScalarRealization.moduleDerivedExtension q').mapIso
      (LA.mapDerivedCategoryFactors.app K) ≪≫
      asIso (ConstantScalarRealization.moduleRepresentative q' K') ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (liftedTensorComparison q) (.up ℤ)).app K).symm ≪≫
      (LB.mapDerivedCategoryFactors.app Kq).symm ≪≫ LB.mapDerivedCategory.mapIso r.symm
  let s : D ≅ ConstantScalarRealization.derivedExtension J q' :=
    (pbcDerivedScalarAdjunction (adicConstantMap X q)).leftAdjointUniq
      (ConstantScalarRealization.derivedAdjunction J q')
  let c := (ConstantScalarRealization.comparisonIso J q').app
    (LA.mapDerivedCategory.obj (DerivedCategory.Q.obj K))
  let c₀ : D.obj ((finitePerfectAdicDerivedConstant X A).obj (DerivedCategory.Q.obj K)) ≅
      (finitePerfectAdicDerivedConstant X B).obj
        ((ConstantScalarRealization.moduleDerivedExtension q).obj (DerivedCategory.Q.obj K)) :=
    D.mapIso ((constantFactorization X A).app _) ≪≫ s.app _ ≪≫ c ≪≫
      cB.mapIso r' ≪≫ ((constantFactorization X B).app _).symm
  exact ⟨D.mapIso ((finitePerfectAdicDerivedConstant X A).mapIso e) ≪≫ c₀ ≪≫
    (finitePerfectAdicDerivedConstant X B).mapIso
      ((ConstantScalarRealization.moduleDerivedExtension q).mapIso e).symm⟩

end AlgebraicGeometry.Scheme
