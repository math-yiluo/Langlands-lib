import Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement
import Langlands.Global.RankinSelberg.CuspidalWhittakerExpansionProof
import Langlands.Global.RankinSelberg.EqualAnalyticCharacter

/-! # Cuspidal operator multiplicity one from comparison of actual Whittaker functions

The analytic input is stated explicitly as `CuspidalWhittakerModelComparisonStatement`.
The reconstruction uses the published Whittaker expansion for these exact realizations.
-/

noncomputable section
universe u
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.RankinSelbergGlobal

local instance multiplicitySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance multiplicitySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- The remaining global analytic comparison input: a full operator equivalence identifies
the actual Whittaker functions up to one scalar, independent of the vector and group point.
No uniqueness assertion for arbitrary algebraic Harish-Chandra module functionals is made. -/
def CuspidalWhittakerModelComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : CuspidalOperatorRealization F r) (e : T.Equivalence T')
    (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∃ c : ℂ, ∀ (v : T.Space) (g : Points F (r + 1)),
        cuspWhittaker F T' ψ (e v) g = c * cuspWhittaker F T ψ v g

namespace CuspidalMultiplicityOne

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T T' : CuspidalOperatorRealization F r)

local instance : AddCommGroup (RationalInvariantFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance : AddCommGroup T.Space := Submodule.addCommGroup _
local instance : AddCommGroup T'.Space := Submodule.addCommGroup _

/-- Proportional actual Whittaker functions reconstruct proportional cusp functions. -/
theorem cuspFunction_eq_mul_of_whittaker_eq_mul
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (v : T.Space) (v' : T'.Space) (c : ℂ)
    (h : ∀ g, cuspWhittaker F T' ψ v' g = c * cuspWhittaker F T ψ v g)
    (g : Points F (r + 1)) :
    cuspFunction F T' v' g = c * cuspFunction F T v g := by
  have hs := (cuspidalWhittakerExpansionStatement_proof F r T ψ hψ v g).2
  have hs' := (cuspidalWhittakerExpansionStatement_proof F r T' ψ hψ v' g).2
  simp_rw [h] at hs'
  exact hs'.unique (hs.mul_left c)

/-- Equality of actual cusp functions reflects equality in the common stable ambient space. -/
theorem inclusion_eq_smul_of_cuspFunction_eq_mul
    (v : T.Space) (v' : T'.Space) (c : ℂ)
    (h : ∀ g, cuspFunction F T' v' g = c * cuspFunction F T v g) :
    (v' : StableAutomorphicFunctions F (r + 1)) =
      c • (v : StableAutomorphicFunctions F (r + 1)) := by
  apply stableAutomorphicInclusion_injective F (r + 1)
  apply automorphicToContinuous_injective F (r + 1)
  change T'.realization.toContinuous v' = c • T.realization.toContinuous v
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change ContinuousRationalFunctions.evaluate F (r + 1) (T'.realization.toContinuous v') g =
    c * ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v) g
  have hh := h ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)
  simpa only [Unfolding.cuspFunction_apply_eq,
    ContinuousMulEquiv.apply_symm_apply] using hh

/-- One scalar comparison along an equivalence forces equality of the two realizations. -/
theorem realization_eq_of_whittaker_comparison
    (e : T.Equivalence T') (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (c : ℂ)
    (h : ∀ (v : T.Space) (g : Points F (r + 1)),
      cuspWhittaker F T' ψ (e v) g = c * cuspWhittaker F T ψ v g) :
    T.realization = T'.realization := by
  have hi (v : T.Space) :
      (e v : StableAutomorphicFunctions F (r + 1)) =
        c • (v : StableAutomorphicFunctions F (r + 1)) :=
    inclusion_eq_smul_of_cuspFunction_eq_mul F T T' v (e v) c
      (cuspFunction_eq_mul_of_whittaker_eq_mul F T T' ψ hψ v (e v) c (h v))
  have hc : c ≠ 0 := by
    intro hc
    obtain ⟨v', hv'⟩ := exists_ne (0 : T'.Space)
    have heq : e (e.symm v') = v' := e.apply_symm_apply v'
    have hh : (v' : StableAutomorphicFunctions F (r + 1)) =
        c • (e.symm v' : StableAutomorphicFunctions F (r + 1)) :=
      (congrArg Subtype.val heq).symm.trans (hi (e.symm v'))
    rw [hc, zero_smul] at hh
    exact hv' (Subtype.ext hh)
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v hv
    have he := (e ⟨v, hv⟩).property
    rw [hi] at he
    have hh := T'.realization.toSubmodule.smul_mem c⁻¹ he
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh
  · intro v' hv'
    have he := (e.symm ⟨v', hv'⟩).property
    have hh := T.realization.toSubmodule.smul_mem c he
    have heq : e (e.symm ⟨v', hv'⟩) = ⟨v', hv'⟩ := e.apply_symm_apply _
    have hval : v' = c • (e.symm ⟨v', hv'⟩ : StableAutomorphicFunctions F (r + 1)) :=
      (congrArg Subtype.val heq).symm.trans (hi (e.symm ⟨v', hv'⟩))
    exact hval.symm ▸ hh

end CuspidalMultiplicityOne

/-- The exact unconditional multiplicity-one target follows from the named global
Whittaker comparison input. The comparison input remains unproved here. -/
def CuspidalOperatorMultiplicityOneReductionStatement : Prop :=
  CuspidalWhittakerModelComparisonStatement.{u} →
    CuspidalOperatorMultiplicityOneStatement.{u}

/-- Reconstruction reduction, using the published exact cuspidal Whittaker expansion. -/
theorem cuspidalOperatorMultiplicityOneReduction :
    CuspidalOperatorMultiplicityOneReductionStatement.{u} := by
  intro h F _ _ _ r T T' ⟨e⟩
  let ψ := EqualAnalytic.standardCharacter F
  have hψ : IsStandardAdditiveCharacter F ψ := by
    refine ⟨EqualAnalytic.continuous_standardCharacter F, ?_,
      EqualAnalytic.standardCharacter_algebraMap F, ?_⟩
    · obtain ⟨x, hx⟩ := CuspidalWhittaker.exists_adelicCharacter_ne_one F
      intro hh
      apply hx
      apply (EqualAnalytic.standardCharacter_eq_one_iff F x).mp
      exact congrArg (fun χ : AddChar (Adeles F) ℂ => χ x) hh
    · intro x
      exact Circle.norm_coe _
  obtain ⟨c, hc⟩ := h F r T T' e ψ hψ
  exact CuspidalMultiplicityOne.realization_eq_of_whittaker_comparison F T T' e ψ hψ c hc

end Langlands.Automorphic
