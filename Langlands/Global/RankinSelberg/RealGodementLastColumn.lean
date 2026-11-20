import Langlands.Global.RankinSelberg.RealGodementStepFubini
import Langlands.Global.RankinSelberg.RealGodementCompactSupport

/-! # The last-column chart of the real Godement open cell -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (d : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent d ℝ) := borel _
private local instance (d : ℕ) : BorelSpace (GeneralLinear.upperUnipotent d ℝ) := ⟨rfl⟩

private def lastColumnIndex (m : ℕ) : Fin m ⊕ UpperEntryPair m ≃ UpperEntryPair (m + 1) where
  toFun
    | .inl i => ⟨(i.rev.castSucc, Fin.last m), Fin.castSucc_lt_last _⟩
    | .inr q => ⟨(q.val.1.castSucc, q.val.2.castSucc), q.property⟩
  invFun q :=
    have hrow : q.val.1 ≠ Fin.last m := Fin.ne_of_lt (lt_of_lt_of_le q.property (Fin.le_last _))
    if h : q.val.2 = Fin.last m then
      .inl (q.val.1.castPred hrow).rev
    else
      .inr ⟨(q.val.1.castPred hrow, q.val.2.castPred h), q.property⟩
  left_inv q := by
    cases q with
    | inl i => simp only [dite_true, Fin.castPred_castSucc, Fin.rev_rev]
    | inr q => simp only [Fin.castSucc_ne_last, dite_false, Fin.castPred_castSucc]
  right_inv q := by
    dsimp
    split_ifs with h
    · apply Subtype.ext
      apply Prod.ext
      · change ((q.val.1.castPred _).rev.rev).castSucc = q.val.1
        rw [Fin.rev_rev, Fin.castSucc_castPred]
      · exact h.symm
    · have hrow : q.val.1 ≠ Fin.last m :=
        Fin.ne_of_lt (lt_of_lt_of_le q.property (Fin.le_last _))
      exact Subtype.ext (Prod.ext (Fin.castSucc_castPred _ hrow) (Fin.castSucc_castPred _ h))

/-- Join the reversed last column with the upper-left unipotent block. -/
def lastColumnChart (t : ℕ) :
    ((Fin (t + 1) → ℝ) × GeneralLinear.upperUnipotent (t + 1) ℝ) ≃ᵐ
      GeneralLinear.upperUnipotent (t + 2) ℝ :=
  let m := t + 1
  ((MeasurableEquiv.refl (Fin m → ℝ)).prodCongr (upperEntryCoordinates m).toMeasurableEquiv).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ UpperEntryPair m => ℝ)).symm.trans
      ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) (lastColumnIndex m)).trans
        (upperEntryCoordinates (m + 1)).symm.toMeasurableEquiv))

/-- The chart transports the product of the two specified entry measures. -/
theorem measurePreserving_lastColumnChart (t : ℕ) (a : ℝˣ) :
    MeasurePreserving (lastColumnChart t)
      ((rowMeasure (realSelfDualMeasure a) (t + 1)).prod (upperStepHaar t a))
      (upperStepHaar (t + 1) a) := by
  let m := t + 1
  let ρ := (realSelfDualMeasure a).measure
  let ν := rowMeasure (realSelfDualMeasure a) m
  let e := (upperEntryCoordinates m (K := ℝ)).toMeasurableEquiv
  let e' := (upperEntryCoordinates (m + 1) (K := ℝ)).toMeasurableEquiv
  let : SigmaFinite (upperStepHaar t a) := upperStepHaar_sigmaFinite t a
  have hU : MeasurePreserving e.symm (upperEntryProductMeasure (realSelfDualMeasure a) m)
      (upperStepHaar t a) := ⟨e.symm.measurable, rfl⟩
  have hU' : MeasurePreserving e'.symm (upperEntryProductMeasure (realSelfDualMeasure a) (m + 1))
      (upperStepHaar (t + 1) a) := ⟨e'.symm.measurable, rfl⟩
  exact hU'.comp ((measurePreserving_piCongrLeft (fun _ : UpperEntryPair (m + 1) => ρ)
    (lastColumnIndex m)).comp
    ((measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ UpperEntryPair m => ρ)).comp
      ((MeasurePreserving.id ν).prod (hU.symm e.symm))))

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "V" => (Fin (t + 1) → ℝ)
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ

private theorem lastColumnChart_entry (x : V) (u : N) (q : Fin m ⊕ UpperEntryPair m) :
    let p := lastColumnIndex m q
    (lastColumnChart t (x, u)).val.val p.val.1 p.val.2 =
      Sum.elim x (upperEntryCoordinates m u) q := by
  change ((upperEntryCoordinates (m + 1) (K := ℝ)).symm
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (lastColumnIndex m)
      (Sum.elim x (upperEntryCoordinates m u)))).val.val _ _ = _
  rw [upperEntryCoordinates_symm_upper _ (lastColumnIndex m q).property]
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) (lastColumnIndex m) _ q

/-- The upper-left square of the chart is the lower-rank unipotent input. -/
theorem lastColumnChart_upperLeft (x : V) (u : N) (i j : Fin m) :
    (lastColumnChart t (x, u)).val.val i.castSucc j.castSucc = u.val.val i j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · let q : UpperEntryPair m := ⟨(i, j), hij⟩
    exact (lastColumnChart_entry x u (.inr q)).trans (upperEntryCoordinates_apply u q)
  · rw [UpperUnipotent.entry_diag, UpperUnipotent.entry_diag]
  · rw [UpperUnipotent.entry_eq_zero _ (show j.castSucc < i.castSucc from hji),
      UpperUnipotent.entry_eq_zero _ hji]

/-- The entries in the last column occur in reversed order. -/
theorem lastColumnChart_last (x : V) (u : N) (i : Fin m) :
    (lastColumnChart t (x, u)).val.val i.rev.castSucc (Fin.last m) = x i :=
  lastColumnChart_entry x u (.inl i)

/-- The standard character splits into its last-column and lower-rank factors. -/
theorem standardCharacter_lastColumnChart (a : ℝˣ) (x : V) (u : N) :
    (standardCharacter (realScaledCharacter a) m (lastColumnChart t (x, u)) : ℂ) =
      (realScaledCharacter a).complex (x 0) * (standardCharacter (realScaledCharacter a) t u : ℂ) := by
  simp only [standardCharacter_apply, Fin.sum_univ_castSucc]
  rw [mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  · apply Finset.sum_congr rfl
    intro i _
    rw [show i.castSucc.succ = i.succ.castSucc from rfl, lastColumnChart_upperLeft]
  · simpa only [Fin.rev_zero, Fin.succ_last] using lastColumnChart_last x u 0

/-- After Weyl reversal the last column and smaller unipotent block form the
trailing rectangle in the real Godement section. -/
theorem lastRows_lastColumnChart (x : V) (u : N) (g : H) :
    lastRows (weylLong (m + 1) ℝ * (lastColumnChart t (x, u)).val * g).val =
      joinFirstColumn x (weylLong m ℝ * u.val * weylLong m ℝ).val * (weylLong (m + 1) ℝ * g).val := by
  let w := weylLong (m + 1) ℝ
  let U := (lastColumnChart t (x, u)).val
  have hRows : lastRows (w * U * w).val = joinFirstColumn x (weylLong m ℝ * u.val * weylLong m ℝ).val := by
    ext i j
    change (w * U * w).val i.succ j = _
    rw [weylLong_conjugate_entry, Fin.rev_succ]
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [Fin.rev_zero, joinFirstColumn_zero]
      exact lastColumnChart_last x u i
    · rw [Fin.rev_succ, joinFirstColumn_succ, weylLong_conjugate_entry]
      exact lastColumnChart_upperLeft x u i.rev k.rev
  have hProduct : w * U * g = (w * U * w) * (w * g) := by
    rw [mul_assoc (w * U), ← mul_assoc w w g, weylLong_mul_self, one_mul]
  change lastRows (w * U * g).val = _
  rw [hProduct, Units.val_mul]
  change lastRows (w * U * w).val * (w * g).val = _
  rw [hRows]

/-- The last-column coordinates give the exact product measure, phase, and
trailing rectangle of the open-cell evaluation of a Godement section. -/
def RealGodementLastColumnStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ), let rank := t + 1
  MeasurePreserving (lastColumnChart t)
    ((rowMeasure (realSelfDualMeasure a) rank).prod (upperStepHaar t a)) (upperStepHaar (t + 1) a) ∧
  ∀ (x : Fin rank → ℝ) (u : GeneralLinear.upperUnipotent rank ℝ) (g : Langlands.GeneralLinear (rank + 1) ℝ),
    (standardCharacter (realScaledCharacter a) rank (lastColumnChart t (x, u)) : ℂ) =
      (realScaledCharacter a).complex (x 0) * (standardCharacter (realScaledCharacter a) t u : ℂ) ∧
    lastRows (weylLong (rank + 1) ℝ * (lastColumnChart t (x, u)).val * g).val =
      joinFirstColumn x (weylLong rank ℝ * u.val * weylLong rank ℝ).val * (weylLong (rank + 1) ℝ * g).val

theorem realGodementLastColumn : RealGodementLastColumnStatement := by
  intro t a rank
  exact ⟨measurePreserving_lastColumnChart t a, fun x u g =>
    ⟨standardCharacter_lastColumnChart a x u, lastRows_lastColumnChart x u g⟩⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
