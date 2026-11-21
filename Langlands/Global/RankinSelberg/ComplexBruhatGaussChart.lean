import Langlands.Global.RankinSelberg.ComplexGaussSolve

/-! # The actual Bruhat cells in smooth Gauss charts -/

noncomputable section

open Set
open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatGaussChart

open Langlands.GeneralLinear
open Langlands.GeneralLinear.UpperBruhatCoordinates (upperBruhatCellMap_surjective continuous_generalLinear_of_val)
open ComplexGaussSolve (gaussDomain gaussCoordinates gaussUpper isOpen_gaussDomain contDiffOn_gaussCoordinates
  gaussUpper_mem gaussUpper_mul_inverse gaussDomain_of_factor recover_lower_of_factor oppositePoint_mem_lower
  oppositePoint_injective)
open ComplexModulusOpenCell (groupTranspose_val)
open ComplexOppositeCompactChart (Coordinates oppositePoint contDiff_oppositePoint_val)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => upperTriangularSubgroup n ℂ

variable {n : ℕ}

/-- Gauss pivot domain in the ambient matrix space, after multiplication by the inverse
of the chosen permutation matrix. -/
def chartMatrixDomain (w : Equiv.Perm (Fin n)) : Set (Mat n) :=
  (fun X => X * (permutation n ℂ w)⁻¹.val) ⁻¹' gaussDomain n

/-- The corresponding open chart in the group. -/
def chartDomain (w : Equiv.Perm (Fin n)) : Set (G n) :=
  Units.val ⁻¹' chartMatrixDomain w

/-- Lower column-solve coordinates on the chart. -/
def chartCoordinates (w : Equiv.Perm (Fin n)) (X : Mat n) : Coordinates n :=
  gaussCoordinates (X * (permutation n ℂ w)⁻¹.val)

/-- The upper triangular factor on the chart. -/
def chartUpper (w : Equiv.Perm (Fin n)) (g : G n) : G n :=
  gaussUpper (g * (permutation n ℂ w)⁻¹)

/-- The chosen representative for a vector of lower coordinates. -/
def chartSection (w : Equiv.Perm (Fin n)) (z : Coordinates n) : G n :=
  (oppositePoint z)⁻¹ * permutation n ℂ w

/-- Whether a lower entry belongs to the conjugate of the original upper unipotent. -/
def allowedLowerEntry (w : Equiv.Perm (Fin n)) (p : UpperEntryPair n) : Prop :=
  w.symm p.val.2 < w.symm p.val.1

/-- The coordinate subspace of the actual Bruhat cell in its Gauss chart. -/
def cellCoordinates (w : Equiv.Perm (Fin n)) : Set (Coordinates n) :=
  {z | ∀ p : UpperEntryPair n, ¬ allowedLowerEntry w p → z p = 0}

private def shiftByPermutation (w : Equiv.Perm (Fin n)) : Mat n →L[ℝ] Mat n :=
  (ContinuousLinearMap.mul ℝ (Mat n)).flip (permutation n ℂ w)⁻¹.val

theorem isOpen_chartMatrixDomain (w : Equiv.Perm (Fin n)) : IsOpen (chartMatrixDomain w) :=
  (isOpen_gaussDomain n).preimage (shiftByPermutation w).continuous

theorem isOpen_chartDomain (w : Equiv.Perm (Fin n)) : IsOpen (chartDomain w) :=
  (isOpen_chartMatrixDomain w).preimage Units.continuous_val

theorem contDiffOn_chartCoordinates (w : Equiv.Perm (Fin n)) :
    ContDiffOn ℝ ∞ (chartCoordinates w) (chartMatrixDomain w) :=
  (contDiffOn_gaussCoordinates n).comp (shiftByPermutation w).contDiff.contDiffOn fun _ h => h

theorem continuous_chartSection (w : Equiv.Perm (Fin n)) : Continuous (chartSection w) := by
  have h : Continuous (oppositePoint (n := n)) := continuous_generalLinear_of_val (contDiff_oppositePoint_val n).continuous
  exact h.inv.mul continuous_const

theorem chartUpper_mem (w : Equiv.Perm (Fin n)) (g : G n) (hg : g ∈ chartDomain w) : chartUpper w g ∈ B n :=
  gaussUpper_mem _ hg

theorem chart_factorization (w : Equiv.Perm (Fin n)) (g : G n) :
    chartUpper w g * chartSection w (chartCoordinates w g.val) = g := by
  change gaussUpper (g * (permutation n ℂ w)⁻¹) *
    ((oppositePoint (gaussCoordinates (g * (permutation n ℂ w)⁻¹).val))⁻¹ * permutation n ℂ w) = g
  rw [← mul_assoc, gaussUpper_mul_inverse, inv_mul_cancel_right]

theorem chart_recover (w : Equiv.Perm (Fin n)) (b : B n) (z : Coordinates n) :
    b.val * chartSection w z ∈ chartDomain w ∧
      chartCoordinates w (b.val * chartSection w z).val = z ∧ chartUpper w (b.val * chartSection w z) = b.val := by
  let U := oppositePoint z
  have hU : U⁻¹ ∈ lowerUnipotent n ℂ := inv_mem (oppositePoint_mem_lower z)
  have hX : b.val * chartSection w z * (permutation n ℂ w)⁻¹ = b.val * U⁻¹ := by
    change b.val * (U⁻¹ * permutation n ℂ w) * (permutation n ℂ w)⁻¹ = b.val * U⁻¹
    group
  have hg : b.val * chartSection w z ∈ chartDomain w := by
    change (b.val * chartSection w z * (permutation n ℂ w)⁻¹).val ∈ gaussDomain n
    rw [hX]
    exact gaussDomain_of_factor b _ hU
  have hCoord : chartCoordinates w (b.val * chartSection w z).val = z := by
    apply oppositePoint_injective n
    change oppositePoint (gaussCoordinates (b.val * chartSection w z * (permutation n ℂ w)⁻¹).val) = U
    rw [hX, recover_lower_of_factor b _ hU, inv_inv]
  have hB : chartUpper w (b.val * chartSection w z) = b.val := by
    unfold chartUpper gaussUpper
    rw [show gaussCoordinates (b.val * chartSection w z * (permutation n ℂ w)⁻¹).val = z from hCoord]
    rw [hX, inv_mul_cancel_right]
  exact ⟨hg, hCoord, hB⟩

theorem chart_left_mul (w : Equiv.Perm (Fin n)) (b : B n) (g : G n) (hg : g ∈ chartDomain w) :
    b.val * g ∈ chartDomain w ∧ chartCoordinates w (b.val * g).val = chartCoordinates w g.val ∧
      chartUpper w (b.val * g) = b.val * chartUpper w g := by
  let c : B n := ⟨b.val * chartUpper w g, mul_mem b.2 (chartUpper_mem w g hg)⟩
  have he : b.val * g = c.val * chartSection w (chartCoordinates w g.val) := by
    change b.val * g = (b.val * chartUpper w g) * chartSection w (chartCoordinates w g.val)
    rw [mul_assoc, chart_factorization]
  rw [he]
  exact chart_recover w c _

private theorem oppositePoint_entry (z : Coordinates n) (p : UpperEntryPair n) :
    (oppositePoint z).val p.val.2 p.val.1 = z p := by
  change (ComplexModulusOpenCell.groupTranspose ((upperEntryCoordinates (K := ℂ) n).symm z).val).val _ _ = _
  rw [groupTranspose_val, Matrix.transpose_apply, upperEntryCoordinates_symm_upper _ p.2]

/-- The permitted lower entries characterize the conjugated unipotent coordinate of a cell. -/
theorem conjugate_oppositePoint_mem (w : Equiv.Perm (Fin n)) (z : Coordinates n) :
    (permutation n ℂ w)⁻¹ * oppositePoint z * permutation n ℂ w ∈ permutationUnipotentMinus n ℂ w ↔
      z ∈ cellCoordinates w := by
  let P := permutation n ℂ w
  let U := oppositePoint z
  have hUL := (mem_lowerUnipotent_iff n ℂ U).mp (oppositePoint_mem_lower z)
  have he (i j : Fin n) : (P⁻¹ * U * P).val i j = U.val (w i) (w j) := by
    have h := permutation_conjugate_entry n ℂ w⁻¹ U i j
    rw [← permutation_inv n ℂ w] at h
    simpa only [inv_inv] using h
  constructor
  · intro hz p hp
    have hU := (mem_upperUnipotent_iff n ℂ _).mp ((mem_permutationUnipotentMinus_iff n ℂ w _).mp hz).1
    have hne : w.symm p.val.2 ≠ w.symm p.val.1 := fun h => p.2.ne (w.symm.injective h).symm
    have hlt : w.symm p.val.1 < w.symm p.val.2 :=
      lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm hne)
    have h0 := hU.1 _ _ hlt
    change (P⁻¹ * U * P).val _ _ = 0 at h0
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, oppositePoint_entry] at h0
    exact h0
  · intro hz
    apply (mem_permutationUnipotentMinus_iff n ℂ w _).mpr
    refine ⟨(mem_upperUnipotent_iff n ℂ _).mpr ⟨?_, fun i => (he i i).trans (hUL.2 (w i))⟩, ?_⟩
    · intro i j hji
      change (P⁻¹ * U * P).val i j = 0
      rw [he]
      rcases lt_or_gt_of_ne (fun h => hji.ne (w.injective h).symm) with hij | hij
      · exact hUL.1 _ _ hij
      · let p : UpperEntryPair n := ⟨(w j, w i), hij⟩
        have hn : ¬ allowedLowerEntry w p := by simpa [allowedLowerEntry, p] using hji.not_gt
        exact (oppositePoint_entry z p).trans (hz p hn)
    · change P * (P⁻¹ * U * P) * P⁻¹ ∈ lowerUnipotent n ℂ
      rw [show P * (P⁻¹ * U * P) * P⁻¹ = U by group]
      exact oppositePoint_mem_lower z

/-- A smooth Gauss chart covers each actual complex upper Bruhat cell and its cell
coordinates are the specified linear coordinate subspace. -/
def ComplexBruhatGaussChartStatement : Prop :=
  ∀ (n : ℕ) (w : Equiv.Perm (Fin n)), IsOpen (chartDomain w) ∧
    ContDiffOn ℝ ∞ (chartCoordinates w) (chartMatrixDomain w) ∧
    ∀ g : G n, g ∈ upperBruhatCell n ℂ w ↔
      g ∈ chartDomain w ∧ chartCoordinates w g.val ∈ cellCoordinates w

set_option maxHeartbeats 850000 in
theorem complexBruhatGaussChart : ComplexBruhatGaussChartStatement := by
  intro n w
  refine ⟨isOpen_chartDomain w, contDiffOn_chartCoordinates w, fun g => ⟨?_, ?_⟩⟩
  · intro hg
    obtain ⟨⟨b, v⟩, h⟩ := upperBruhatCellMap_surjective w (K := ℂ) ⟨g, hg⟩
    have hg' : b.val * permutation n ℂ w * v.val = g := congrArg Subtype.val h
    let P := permutation n ℂ w
    let l := P * v.val * P⁻¹
    have hl : l ∈ lowerUnipotent n ℂ := ((mem_permutationUnipotentMinus_iff n ℂ w _).mp v.2).2
    have he : g * P⁻¹ = b.val * l := by rw [← hg']; dsimp only [l, P]; group
    have hgDom : g ∈ chartDomain w := by
      change (g * P⁻¹).val ∈ gaussDomain n
      rw [he]
      exact gaussDomain_of_factor b l hl
    refine ⟨hgDom, (conjugate_oppositePoint_mem w _).mp ?_⟩
    have hLower : oppositePoint (chartCoordinates w g.val) = l⁻¹ := by
      change oppositePoint (gaussCoordinates (g * P⁻¹).val) = l⁻¹
      rw [he, recover_lower_of_factor b _ hl]
    rw [hLower]
    change P⁻¹ * l⁻¹ * P ∈ permutationUnipotentMinus n ℂ w
    rw [show P⁻¹ * l⁻¹ * P = v.val⁻¹ by dsimp only [l]; group]
    exact inv_mem v.2
  · rintro ⟨hg, hz⟩
    let z := chartCoordinates w g.val
    let P := permutation n ℂ w
    let v := (P⁻¹ * oppositePoint z * P)⁻¹
    have hv : v ∈ permutationUnipotentMinus n ℂ w := inv_mem ((conjugate_oppositePoint_mem w z).mpr hz)
    have hvB : v ∈ B n := upperUnipotent_le_upperTriangular n ℂ (permutationUnipotentMinus_le_upperUnipotent n ℂ w hv)
    refine ⟨chartUpper w g, chartUpper_mem w g hg, v, hvB, ?_⟩
    calc
      g = chartUpper w g * chartSection w z := (chart_factorization w g).symm
      _ = chartUpper w g * P * v := by
        change chartUpper w g * ((oppositePoint z)⁻¹ * P) = chartUpper w g * P * v
        dsimp only [v]
        group

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatGaussChart
