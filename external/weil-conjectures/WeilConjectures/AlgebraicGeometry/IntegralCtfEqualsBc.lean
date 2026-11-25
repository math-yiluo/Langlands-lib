/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Topology.Instances.ZMod
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantSquareZeroTorExample
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel

/-! # Integral and rational constructible complexes have finite Tor amplitude

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-integral-criterion/lem-integral-ctf-equals-bc.md and its proof
(blueprint: proposition-ctf-equals-bc).

The categories are ordinary uncompleted internal-module derived categories. The scalar
examples are stated on explicit helper definitions of this module.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj MonoidalCategory ZeroObject

namespace AlgebraicGeometry.ProEtale

/-- Constructible modules have amplitude [-1,0], or [0,0] for field coefficients;
bounded constructible complexes inherit the indicated cohomological interval, enlarged
by one only in the integral case. In particular Dctf and Dbc have identical object
predicates, hence identical full subcategories and ambient morphisms.

Source: latest blueprint proposition-ctf-equals-bc, clauses (1), (2) and their consequence
(blueprint: proposition-ctf-equals-bc).

Proof:
1. The integral clauses come from det-def-localizing-closure-ctf-equals-bc
(localizingClosure_ctf_equals_bc). Constructible modules have amplitude [-1,0], and bounded
constructible complexes with cohomology in [a,b] have amplitude [a-1,b]. The object predicates
of Dctf and Dbc are equal. That theorem combines lem-sfb-padic-constant-local-model-tor,
lem-sfb-stratified-tor-interval-devissage and lem-sfb-cohomology-tor-interval. Its field
clause gives amplitude [0,0] for constructible modules over E, Q_ell or Qlb.
2. Over a field, let K be in Dbc with cohomology in [a,b]. Each H^q(K) is constructible by
the definition in det-def-sfb-constructible-tor-amplitude, so it has amplitude [0,0] by
step 1. lem-sfb-cohomology-tor-interval with c=d=0 then gives amplitude [a,b]. No
completeness hypothesis is used. -/
theorem integral_ctf_equals_bc (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ :
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E)) ∨
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
      IsConstantModelConstructible Λ.X X M → DerivedCategory.torAmplitudeIn _ (-1) 0
        ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
        (a b : ℤ), a ≤ b → constantModelBoundedConstructible Λ.X X K →
      DerivedCategory.homologyConcentratedIn a b K →
      DerivedCategory.torAmplitudeIn _ (a - 1) b K) ∧
    ((Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) →
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
        IsConstantModelConstructible Λ.X X M → DerivedCategory.torAmplitudeIn _ 0 0
          ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
      (∀ (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
          (a b : ℤ), a ≤ b → constantModelBoundedConstructible Λ.X X K →
        DerivedCategory.homologyConcentratedIn a b K →
        DerivedCategory.torAmplitudeIn _ a b K)) ∧
    (constantModelBoundedConstructible Λ.X X ⊓ DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ.X X := by
  obtain ⟨h, hfield⟩ := localizingClosure_ctf_equals_bc ℓ X Λ.X hΛ
  refine ⟨h.1, h.2.1, ?_, h.2.2.1⟩
  intro hΛfield
  have hmod := hfield hΛfield
  refine ⟨hmod, ?_⟩
  intro K a b hab hK hbound
  have htor := torAmplitudeIn_of_cohomology_interval X Λ K a b 0 0 hab le_rfl
    (fun q hq ↦ by
      by_cases hqa : q < a
      · exact (DerivedCategory.isGE_iff K a).1 hbound.1 q hqa
      · exact (DerivedCategory.isLE_iff K b).1 hbound.2 q (by
          simp only [Set.mem_Icc] at hq
          omega))
    (fun q _ ↦ hmod _ (hK.2 q))
  simpa only [add_zero] using htor

namespace IntegralCriterionProof

open Opposite

end IntegralCriterionProof

end AlgebraicGeometry.ProEtale
