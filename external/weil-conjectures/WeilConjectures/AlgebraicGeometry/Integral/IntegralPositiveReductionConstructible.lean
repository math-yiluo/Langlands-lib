/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-! # Constructibility of positive integral reductions -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem fixedCriterion
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u}) [IsNoetherian X]
    (e : FiniteDiscreteOrdinary.Encoding A X)
    (M : DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :
    constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X M ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
        (e.fixedDerived.functor.obj M) := by
  let F := e.ordinary.functor ⋙ e.fixed.functor
  have hc (q : ℤ) :
      Scheme.IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor _ q).obj (e.ordinaryDerived.functor.obj M)) ↔
      IsConstructible (ULift.{u + 1} A)
        ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj M)) := by
    let d := (FiniteDiscreteOrdinary.fixedIso A X e
      ((DerivedCategory.homologyFunctor _ q).obj (e.ordinaryDerived.functor.obj M))).symm
    let j := (e.ordinary.functor.mapDerivedCategoryHomologyFunctorIso q).app M
    let k := (F.mapDerivedCategoryHomologyFunctorIso q).app M
    let z := d ≪≫ e.fixed.functor.mapIso j.symm ≪≫ k
    exact (Scheme.proEtaleModuleRestriction_constructible_iff X A _).trans
      ⟨isConstructible_of_iso z, isConstructible_of_iso z.symm⟩
  rw [finiteEncoding_constructible A X e M]
  constructor
  · intro hM
    exact DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A)
      (F.bounded_mapDerivedCategory_obj
        (e.ordinary.functor.bounded_of_bounded_mapDerivedCategory_obj hM.1))
      (fun q ↦ exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
        ((hc q).mp (hM.2 q)))
  · intro hM
    obtain ⟨L, hL, ⟨z⟩⟩ := hM
    let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
    have hb : _root_.DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj M) :=
      _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso z
        (C.bounded_mapDerivedCategory_obj hL.1)
    refine ⟨e.ordinary.functor.bounded_mapDerivedCategory_obj
      (F.bounded_of_bounded_mapDerivedCategory_obj hb), fun q ↦ (hc q).mpr ?_⟩
    let H := (_root_.DerivedCategory.homologyFunctor _ q).obj L
    let : Scheme.IsConstructibleSheaf H := hL.2 q
    let j := (C.mapDerivedCategoryHomologyFunctorIso q).app L
    exact isConstructible_of_iso
      (j ≪≫ (_root_.DerivedCategory.homologyFunctor _ q).mapIso z)
      (isConstructible_comparisonUpperStar_obj H)

/-- Positive uniformizer reduction preserves bounded finite constant-model constructibility. -/
theorem integralReduction_constantModelBoundedConstructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K)
    (n : ℕ) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
      ((AdicCompletion.derivedReduction l E X n).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology A := finiteTopology_discrete l E n
  obtain ⟨e, _⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n)
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : (AdicCompletion.derivedReduction l E X n).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  have : e.fixedDerived.functor.IsTriangulated := by
    change (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory.IsTriangulated
    infer_instance
  let F := AdicCompletion.derivedReduction l E X n ⋙ e.fixedDerived.functor
  let B := DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let Q := B.inverseImage F
  let P := ObjectProperty.isoClosure
    (IsConstantModelConstructible (DerivedNakayama.integerRing l E) X)
  have hsingle (M : AdicCompletion.Modules l E X) (hM : P M) :
      Q ((_root_.DerivedCategory.singleFunctor _ 0).obj M) := by
    obtain ⟨M', hM', ⟨j⟩⟩ := hM
    have h := (FiniteModelQuotient.finite_model_sheaf_quotient_constructible
      l E X M' hM' n).choose_spec.2.2.1
    have h' := (fixedCriterion A X e _).mp h
    exact Q.prop_of_iso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso j).symm h'
  have hQ : Q K := _root_.DerivedCategory.prop_of_bounded Q P hsingle K hK.1
    (fun q ↦ ⟨_, hK.2 q, ⟨Iso.refl _⟩⟩)
  exact (fixedCriterion A X e _).mpr hQ

end AlgebraicGeometry.ProEtale
