import Langlands.Automorphic.TransposeContragredient
import Langlands.Global.RankinSelberg.CuspidalTransposeInverseContragredientStatement
import Langlands.Global.RankinSelberg.DualWhittakerCore.DualCuspidal

/-! # Reduction to the actual transpose realization and its intrinsic pairing -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open NumberField Langlands.Automorphic Langlands.GeneralLinear
open scoped CategoryTheory.MonObj

local instance transposeReductionRationalAddCommGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance transposeReductionContinuousAddCommGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance transposeReductionSmoothAddCommGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance transposeReductionFormsAddCommGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance transposeReductionStableAddCommGroup
    (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance transposeReductionSpaceAddCommGroup
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (T : CuspidalOperatorRealization F r) :
    AddCommGroup T.Space := Submodule.addCommGroup _

section Functions

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} (T T' : CuspidalOperatorRealization F r)

private theorem cuspFunction_evaluate (x : T.Space) (g : Points F (r + 1)) :
    cuspFunction F T x g =
      ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous x)
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g) := by
  have h := GroupSchemeFunctions.evaluate_continuousGeneralLinearEquiv_at_point F (r + 1)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F (r + 1)).symm
      (T.realization.toContinuous x)) g
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

set_option maxHeartbeats 800000 in
/-- Equality of actual continuous functions under transpose pullback gives exactly the
dual cusp function appearing in the target statement, including its long Weyl element. -/
theorem cuspFunction_eq_dualFunction_of_transposeDual
    (x : T.Space) (x' : T'.Space)
    (h : T'.realization.toContinuous x' =
      ContinuousRationalFunctions.transposeDual (T.realization.toContinuous x)) :
    cuspFunction F T' x' = dualFunction F (r + 1) (cuspFunction F T x) := by
  funext g
  rw [cuspFunction_evaluate F T' x' g, h]
  change ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous x)
    (inverseTranspose (r + 1) (Adeles F)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)) = _
  unfold dualFunction
  rw [cuspFunction_evaluate F T x
    ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm _),
    MulEquiv.apply_symm_apply, UnequalAnalytic.weylLong_eq_rational F (r + 1)]
  exact (ContinuousRationalFunctions.evaluate_rational F (r + 1)
    (T.realization.toContinuous x) (weylLong (r + 1) F) _).symm

end Functions

/-- B1: each actual cuspidal realization has an actual cuspidal transpose realization,
with all three operator covariances and the actual continuous-function formula. -/
def CuspidalTransposeRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    ∃ (T' : CuspidalOperatorRealization F r) (e : T.Space ≃ₗ[ℂ] T'.Space),
      T.realization.IsTransposeIntertwining T'.realization e ∧
        ∀ x : T.Space, T'.realization.toContinuous (e x) =
          ContinuousRationalFunctions.transposeDual (T.realization.toContinuous x)

/-- B2: every actual cuspidal realization has the intrinsic full-operator transpose
contragredient pairing. Its finite, compact, real-Lie and bijectivity clauses are retained. -/
def CuspidalTransposePairingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    T.realization.HasTransposeContragredientPairing

/-- A conditional reduction, with B1 and B2 explicitly retained as open premises. -/
def CuspidalTransposeInverseContragredientReductionStatement : Prop :=
  CuspidalTransposeRealizationStatement.{u} →
    CuspidalTransposePairingStatement.{u} →
      CuspidalTransposeInverseContragredientStatement.{u}

/-- The transpose image supplies every dual cusp function, and the intrinsic pairing
supplies the full-operator contragredient relation. -/
theorem cuspidalTransposeInverseContragredientReduction :
    CuspidalTransposeInverseContragredientReductionStatement.{u} := by
  intro hreal hpair F _ _ _ r T
  obtain ⟨T', e, he, hf⟩ := hreal F r T
  refine ⟨T', he.isContragredientOf (hpair F r T), ?_⟩
  intro x
  exact ⟨e x, cuspFunction_eq_dualFunction_of_transposeDual F T T' x (e x) (hf x)⟩

end Langlands.Global.RankinSelbergGlobal
