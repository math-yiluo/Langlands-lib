import Langlands.Global.RankinSelberg.RealGodementStepChart
import Langlands.Global.RankinSelberg.RealGodementFirstColumn

/-! # The first-column and unipotent integrals of the Godement step -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal Langlands.Whittaker
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (d : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent d ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (GeneralLinear.upperUnipotent d ℝ) := ⟨rfl⟩

private def stepSplitIndex (m : ℕ) : Fin m ⊕ UpperEntryPair m ≃ StepCoordinates m where
  toFun
    | .inl i => ⟨(i, 0), Nat.zero_le _⟩
    | .inr q => ⟨(q.val.1.rev, q.val.2.rev.succ), Nat.succ_le_of_lt (Fin.rev_lt_rev.mpr q.property)⟩
  invFun q := if h : q.val.2 = 0 then .inl q.val.1 else
    .inr ⟨(q.val.1.rev, (q.val.2.pred h).rev), Fin.rev_lt_rev.mpr (by
      have hle := q.property
      have hpos := Fin.pos_iff_ne_zero.mpr h
      change (q.val.2.pred h).val < q.val.1.val
      simp only [Fin.val_pred]
      omega)⟩
  left_inv q := by
    cases q with
    | inl i => simp
    | inr q =>
      simp only [Fin.succ_ne_zero, dite_false, Fin.pred_succ, Fin.rev_rev]
  right_inv q := by
    dsimp
    split_ifs with h
    · exact Subtype.ext (Prod.ext rfl h.symm)
    · apply Subtype.ext
      apply Prod.ext
      · exact Fin.rev_rev _
      · change ((q.val.2.pred h).rev.rev).succ = q.val.2
        rw [Fin.rev_rev, Fin.succ_pred]

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "V" => (Fin (t + 1) → ℝ)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ

private def joinStepChart (d : ℕ) :
    ((Fin (d + 1) → ℝ) × GeneralLinear.upperUnipotent (d + 1) ℝ) ≃ᵐ
      (StepCoordinates (d + 1) → ℝ) :=
  let rank := d + 1
  ((MeasurableEquiv.refl (Fin rank → ℝ)).prodCongr (upperEntryCoordinates rank).toMeasurableEquiv).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin rank ⊕ UpperEntryPair rank => ℝ)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (stepSplitIndex rank)))

theorem upperStepHaar_sigmaFinite (d : ℕ) (a : ℝˣ) : SigmaFinite (upperStepHaar d a) :=
  (upperEntryCoordinates (d + 1) (K := ℝ)).symm.toMeasurableEquiv.sigmaFinite_map
    (μ := upperEntryProductMeasure (realSelfDualMeasure a) (d + 1))

private theorem measurePreserving_joinStepChart (a : ℝˣ) :
    MeasurePreserving (joinStepChart t) ((rowMeasure (realSelfDualMeasure a) m).prod (upperStepHaar t a))
      (stepMeasure m a) := by
  let ρ := (realSelfDualMeasure a).measure
  let ν := rowMeasure (realSelfDualMeasure a) m
  let η := upperEntryProductMeasure (realSelfDualMeasure a) m
  let e := (upperEntryCoordinates m (K := ℝ)).toMeasurableEquiv
  let : SigmaFinite (upperStepHaar t a) := upperStepHaar_sigmaFinite t a
  have hU : MeasurePreserving e.symm η (upperStepHaar t a) :=
    ⟨e.symm.measurable, rfl⟩
  exact (measurePreserving_piCongrLeft (fun _ : StepCoordinates m => ρ) (stepSplitIndex m)).comp
    ((measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ UpperEntryPair m => ρ)).comp
      ((MeasurePreserving.id ν).prod (hU.symm e.symm)))

private theorem joinStepChart_entry (x : V) (u : N) (q : Fin m ⊕ UpperEntryPair m) :
    joinStepChart t (x, u) (stepSplitIndex m q) =
      Sum.elim x (upperEntryCoordinates m u) q := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (stepSplitIndex m) _ q

private theorem stepRectangle_joinStepChart (x : V) (u : N) :
    stepRectangle (joinStepChart t (x, u)) =
      joinFirstColumn x (weylLong m ℝ * u.val * weylLong m ℝ).val := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [joinFirstColumn_zero, stepRectangle,
      dite_eq_left (show (0 : Fin (m + 1)).val ≤ i.val from Nat.zero_le _)]
    exact joinStepChart_entry x u (.inl i)
  · rw [joinFirstColumn_succ]
    have hConj : (weylLong m ℝ * u.val * weylLong m ℝ).val i k = u.val.val i.rev k.rev := by
      exact weylLong_conjugate_entry m ℝ u.val i k
    rw [hConj, stepRectangle]
    by_cases hki : k < i
    · rw [dite_eq_left (show k.succ.val ≤ i.val from Nat.succ_le_of_lt hki)]
      let q : UpperEntryPair m := ⟨(i.rev, k.rev), Fin.rev_lt_rev.mpr hki⟩
      have hIndex : stepSplitIndex m (.inr q) = ⟨(i, k.succ), Nat.succ_le_of_lt hki⟩ := by
        apply Subtype.ext
        change (i.rev.rev, k.rev.rev.succ) = (i, k.succ)
        rw [Fin.rev_rev, Fin.rev_rev]
      rw [← hIndex, joinStepChart_entry]
      exact upperEntryCoordinates_apply u q
    · rw [dite_eq_right (show ¬k.succ.val ≤ i.val from fun h => hki (Nat.lt_of_succ_le h))]
      by_cases he : k = i
      · subst k
        simp only [Fin.val_succ, ite_true, UpperUnipotent.entry_diag]
      · rw [ite_eq_right (show k.succ.val ≠ i.val + 1 from fun hh => he (Fin.ext (Nat.succ.inj hh))),
          UpperUnipotent.entry_eq_zero u (Fin.rev_lt_rev.mpr (lt_of_le_of_ne (le_of_not_gt hki) (Ne.symm he)))]

private theorem stepPhase_eq_rectangle (z : StepCoordinates m → ℝ) :
    stepPhase z = ∑ i : Fin m, stepRectangle z i i.castSucc := by
  rw [stepPhase_eq_upperStepChart]
  simp only [stepRectangle_eq_upperStepChart, Fin.rev_succ, Fin.rev_castSucc]
  exact (Equiv.sum_comp Fin.revPerm (fun i : Fin m => (upperStepChart m z).val i.castSucc i.succ)).symm

private theorem stepPhase_joinStepChart (x : V) (u : N) :
    stepPhase (joinStepChart t (x, u)) = x 0 + ∑ i : Fin t, u.val i.castSucc i.succ := by
  rw [stepPhase_eq_rectangle, stepRectangle_joinStepChart, Fin.sum_univ_succ]
  change x 0 + (∑ i : Fin t, joinFirstColumn x (weylLong m ℝ * u.val * weylLong m ℝ).val i.succ
    i.succ.castSucc) = _
  congr 1
  calc
    _ = ∑ i : Fin t, u.val i.rev.castSucc i.rev.succ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show i.succ.castSucc = i.castSucc.succ from Fin.ext rfl, joinFirstColumn_succ]
      simpa only [Fin.rev_succ, Fin.rev_castSucc] using
        weylLong_conjugate_entry m ℝ u.val i.succ i.castSucc
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin t => u.val i.castSucc i.succ)

/-- The integral in the free first column at frequency `e₀`, with the square
block held fixed. -/
def stepColumnSlice (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) (A : M) : ℂ :=
  ∫ x, Φ (h.val * joinFirstColumn x A * g.val) * (realScaledCharacter a).complex (x 0)
    ∂rowMeasure (realSelfDualMeasure a) m

/-- Fubini for the Godement rectangle with its specified upper-unipotent entry
measure. The joint integral is absolutely integrable. -/
def RealGodementStepFubiniStatement : Prop :=
  ∀ (d : ℕ) (a : ℝˣ) (Φ : 𝓢(Matrix (Fin (d + 1)) (Fin (d + 2)) ℝ, ℂ))
    (h : Langlands.GeneralLinear (d + 1) ℝ) (g : Langlands.GeneralLinear (d + 2) ℝ),
    Integrable (fun p : (Fin (d + 1) → ℝ) × GeneralLinear.upperUnipotent (d + 1) ℝ =>
      Φ (h.val * joinFirstColumn p.1 (weylLong (d + 1) ℝ * p.2.val * weylLong (d + 1) ℝ).val * g.val) *
        (realScaledCharacter a).complex (p.1 0) * (standardCharacter (realScaledCharacter a) d p.2 : ℂ))
      ((rowMeasure (realSelfDualMeasure a) (d + 1)).prod (upperStepHaar d a)) ∧
    kernelSlice a Φ h g = ∫ u, stepColumnSlice a Φ h g (weylLong (d + 1) ℝ * u.val * weylLong (d + 1) ℝ).val *
      (standardCharacter (realScaledCharacter a) d u : ℂ) ∂upperStepHaar d a

theorem realGodementStepFubini : RealGodementStepFubiniStatement := by
  intro d a Φ h g
  let : SigmaFinite (upperStepHaar d a) := upperStepHaar_sigmaFinite d a
  let rank := d + 1
  let Column := Fin rank → ℝ
  let Unipotent := GeneralLinear.upperUnipotent rank ℝ
  let Ψ := kernelSliceIntegrand a Φ h g
  have hJ (p : Column × Unipotent) : Ψ (joinStepChart d p) =
      Φ (h.val * joinFirstColumn p.1 (weylLong rank ℝ * p.2.val * weylLong rank ℝ).val * g.val) *
        (realScaledCharacter a).complex (p.1 0) * (standardCharacter (realScaledCharacter a) d p.2 : ℂ) := by
    obtain ⟨x, u⟩ := p
    simp only [Ψ, rank, kernelSliceIntegrand, stepRectangle_joinStepChart x u, stepPhase_joinStepChart x u,
      AddChar.map_add_eq_mul, standardCharacter_apply, mul_assoc]
  have hI : Integrable (fun p => Ψ (joinStepChart d p))
      ((rowMeasure (realSelfDualMeasure a) rank).prod (upperStepHaar d a)) :=
    (measurePreserving_joinStepChart (t := d) a).integrable_comp_of_integrable
      (integrable_kernelSliceIntegrand a Φ h g)
  refine ⟨hI.congr (Filter.Eventually.of_forall hJ), ?_⟩
  unfold kernelSlice
  rw [← (measurePreserving_joinStepChart (t := d) a).integral_comp' Ψ, integral_prod_symm _ hI]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun u => ?_
  unfold stepColumnSlice
  dsimp only
  rw [← integral_mul_const]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => hJ (x, u))

end Langlands.Global.RankinSelbergGlobal.RealGodement
