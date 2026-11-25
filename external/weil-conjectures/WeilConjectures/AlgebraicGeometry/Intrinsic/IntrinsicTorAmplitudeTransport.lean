/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicResolutionTensorComparison
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral

/-!
# Intrinsic finite-coefficient Tor amplitude transport

## References

* Stacks Project, Tags 00YV, 06YS, 06YU and 08FZ
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem intrinsicTransportAux
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsEquivalence]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (a b : ℤ) (hab : a ≤ b)
    (hcomp : ∀ (L P : CochainComplex
      (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) ℤ)
      (_eL : _root_.DerivedCategory.Q.obj L ≅ F.mapDerivedCategory.obj K)
      (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat P)
      (N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (M : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A))
      (_eM : F.obj N ≅ M) (i : ℤ),
      Nonempty
        ((_root_.DerivedCategory.homologyFunctor _ i).obj
          (Scheme.derivedTensor T A L
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) P f hf hP) ≅
          F.obj ((_root_.DerivedCategory.homologyFunctor _ i).obj
            (((ProEtale.derivedTensor
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj K).obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj N))))) :
    Scheme.HasProEtaleTorAmplitude T A (F.mapDerivedCategory.obj K) a b ↔
      ProEtale.DerivedCategory.torAmplitudeIn
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T a b K := by
  classical
  have hzero (N : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
      IsZero (F.obj N) ↔ IsZero N := by
    constructor
    · intro h
      apply (IsZero.iff_id_eq_zero N).2
      apply F.map_injective
      rw [F.map_id, F.map_zero]
      exact (IsZero.iff_id_eq_zero _).1 h
    · exact F.map_isZero
  have hpoint : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T a b K ↔
      ∀ N i, i < a ∨ b < i →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
          (((ProEtale.derivedTensor
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj K).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj N))) := by
    change (∀ N, _root_.DerivedCategory.homologyConcentratedIn a b _) ↔ _
    constructor
    · intro h N i hi
      rcases hi with hi | hi
      · exact (_root_.DerivedCategory.isGE_iff _ a).1 (h N).1 i hi
      · exact (_root_.DerivedCategory.isLE_iff _ b).1 (h N).2 i hi
    · intro h N
      exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2
          (fun i hi ↦ h N i (Or.inl hi)),
        (_root_.DerivedCategory.isLE_iff _ b).2 (fun i hi ↦ h N i (Or.inr hi))⟩
  rw [hpoint]
  constructor
  · intro h N i hi
    let L := _root_.DerivedCategory.Q.objPreimage (F.mapDerivedCategory.obj K)
    let eL := _root_.DerivedCategory.Q.objObjPreimageIso (F.mapDerivedCategory.obj K)
    obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
    obtain ⟨e⟩ := hcomp L P eL f hf hP
      N (F.obj N) (Iso.refl _) i
    exact (hzero _).1 ((e.isZero_iff).1 (h.2 L P ⟨eL⟩ f hf hP (F.obj N) i hi))
  · intro h
    refine ⟨hab, ?_⟩
    intro L P heL f hf hP M i hi
    obtain ⟨eL⟩ := heL
    let N := F.objPreimage M
    let eM := F.objObjPreimageIso M
    obtain ⟨e⟩ := hcomp L P eL f hf hP
      N M eM i
    exact (e.isZero_iff).2 ((hzero _).2 (h N i hi))

/-- The intrinsic coefficient realization transports the standard pro-etale Tor predicate. -/
theorem intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    (A : Type u) [CommRing A] [Finite A]
    (T : Scheme.{u}) (a b : ℤ) (hab : a ≤ b)
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Scheme.HasProEtaleTorAmplitude T A
        ((finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj K) a b ↔
      ProEtale.DerivedCategory.torAmplitudeIn
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T a b K := by
  let F := finiteCoefficientIntrinsicRealization T A
  let : F.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact T A).1
  exact intrinsicTransportAux A T F K a b hab
    (intrinsic_resolution_tensor_homology_iso A T K)

end AlgebraicGeometry.ProEtale
