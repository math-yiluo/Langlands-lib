import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleBoxes
import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant

/-! # Geometric coefficient growth on the actual dominant matrices -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockLowerUnipotentQuotient
  TwoBlockConvergence TwoBlockLowerFixedSlice TwoBlockJacquet
open scoped BigOperators NNReal ENNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixGrowthTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matrixGrowthValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matrixGrowthLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {t r j k : ℕ} {m : Fin 2 → ℕ}
variable (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))

private theorem rectangleEntries_mul_mem {K : Type*} [Field K] (O : Subring K)
    {a b j k : ℕ} {s : K} {x : Matrix (Fin a) (Fin k) K}
    {y : Matrix (Fin j) (Fin b) K} (hs : s ∈ O)
    (hx : ∀ i l, s * x i l ∈ O) (hy : ∀ i l, s * y i l ∈ O)
    (i l : Coordinates a j k b) : s * rectangleEntries x y i l ∈ O := by
  have hz : s * 0 ∈ O := by rw [mul_zero]; exact O.zero_mem
  have ho : s * 1 ∈ O := by rw [mul_one]; exact hs
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
    simp only [rectangleEntries] <;>
    first | exact hz | exact hx _ _ | exact hy _ _ | split <;> assumption

private theorem rectangleUnipotent_val_mem_box {e : ℕ}
    {x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier}
    {y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier}
    (hx : x ∈ box F (m 0 + 1) k e) (hy : y ∈ box F j (m 1 + 1) e) :
    (rectangleUnipotent h hr x y).val ∈ box F (r + 1) (r + 1) e := by
  have hpow : (F.canonicalTopologicalData.uniformizer : F.Carrier) ^ e ∈
      F.canonicalTopologicalData.Integers := by
    rw [← LocalFactor.PadicAbelian.uniformizerUnit_coe]
    exact pow_mem (uniformizerUnit_isUniformizingElement F).1.le e
  intro i l
  obtain ⟨i, rfl⟩ := (coordinates h hr).surjective i
  obtain ⟨l, rfl⟩ := (coordinates h hr).surjective l
  rw [rectangleUnipotent_five_entry]
  exact rectangleEntries_mul_mem _ hpow hx hy i l

/-- The actual rectangle matrix and its inverse have the same entry bound. -/
theorem rectangleUnipotent_isEntryBounded {e : ℕ}
    {x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier}
    {y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier}
    (hx : x ∈ box F (m 0 + 1) k e) (hy : y ∈ box F j (m 1 + 1) e) :
    IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      e (rectangleUnipotent h hr x y) := by
  have hx' : -x ∈ box F (m 0 + 1) k e := fun i l => by
    simpa only [Matrix.neg_apply, mul_neg] using neg_mem (hx i l)
  have hy' : -y ∈ box F j (m 1 + 1) e := fun i l => by
    simpa only [Matrix.neg_apply, mul_neg] using neg_mem (hy i l)
  have hv := rectangleUnipotent_val_mem_box F h hr hx hy
  have hi := rectangleUnipotent_val_mem_box F h hr hx' hy'
  intro i l
  constructor
  · exact hv i l
  · rw [rectangleUnipotent_inv]
    exact hi i l

/-- Appending an identity block preserves a common entry bound. -/
theorem append_isEntryBounded {e : ℕ} {g : GeneralLinear (t + 1) F.Carrier}
    (hg : IsEntryBounded
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e g) :
    IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      e (append hr g) := by
  have hpow : (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData :
      F.Carrier) ^ e ∈ (ValuativeRel.valuation F.Carrier).integer :=
    pow_mem (uniformizerUnit_isUniformizingElement F).1.le e
  intro i l
  constructor
  · rw [append_entry]
    split_ifs
    · exact (hg _ _).1
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F.Carrier).integer)
    · simpa only [mul_one] using hpow
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F.Carrier).integer)
  · rw [← map_inv, append_entry]
    split_ifs
    · exact (hg _ _).2
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F.Carrier).integer)
    · simpa only [mul_one] using hpow
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F.Carrier).integer)

private theorem integralOpen_isEntryBounded_zero {n : ℕ}
    {g : GeneralLinear (n + 1) F.Carrier} (hg : g ∈ integralOpen F n) :
    IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      0 g := by
  have hg' := (mem_integralOpen F g).mp hg
  intro i l
  simpa only [pow_zero, one_mul] using And.intro (hg'.1 i l) (hg'.2 i l)

/-- Entry bounds for the rectangles and the original group argument add in the
actual JPSS product, including its inverse. -/
theorem matrix_isEntryBounded {e d : ℕ} {g : GeneralLinear (t + 1) F.Carrier}
    {x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier}
    {y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier}
    (hg : IsEntryBounded
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) d g)
    (hx : x ∈ box F (m 0 + 1) k e) (hy : y ∈ box F j (m 1 + 1) e) :
    IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
      (e + d) (matrix h hr g x y) := by
  have hw := integralOpen_isEntryBounded_zero F
    (permutation_mem_integralOpen F r Fin.revPerm)
  have hb : blockWeyl (K := F.Carrier) h hr ∈ integralOpen F r := by
    rw [blockWeyl_permutation]
    exact permutation_mem_integralOpen F r _
  have hb' := integralOpen_isEntryBounded_zero F hb
  simpa only [zero_add, add_zero, matrix, weylLong] using
    (((hw.mul (rectangleUnipotent_isEntryBounded F h hr hx hy)).mul hb').mul
      (append_isEntryBounded F hr hg))

/-- A common coefficient growth base precedes every coefficient-image vector;
the estimate is uniform in both original rectangles. -/
def IsCoefficientRectangleGrowth
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ell : glFunctionals ψ r π) (B : ℝ) : Prop :=
  ∀ W : (coefficientModel π ell).toSubmodule, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F.Carrier)
      (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
      (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
      c ∈ integralOpen F t →
      ‖W.val.val (matrix h hr (Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c) x y)‖ ≤
        C * B ^ torusSize lam

/-- Actual ambient coefficient growth, with no irreducibility or nonzero
functional hypothesis. -/
theorem exists_coefficient_rectangle_growth
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π) (ell : glFunctionals ψ r π) :
    ∃ B : ℝ, 1 ≤ B ∧ IsCoefficientRectangleGrowth F h hr ψ π ell B := by
  obtain ⟨B, hB, hcoeff⟩ := exists_coefficient_growth F ψ π hπ ell
  refine ⟨B * B, one_le_mul_of_one_le_of_one_le hB hB, fun W => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hcoeff W
  obtain ⟨N, hN⟩ := exists_torus_rectangle_box_support F ψ h hr π hπ.1.1 ell W
  refine ⟨C * B ^ N, by positivity, fun lam c x y hc => ?_⟩
  by_cases hw : W.val.val (matrix h hr (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * c) x y) = 0
  · rw [hw, norm_zero]
    positivity
  obtain ⟨hx, hy⟩ := hN lam c x y hc hw
  have htorus := isEntryBounded_torus F (uniformizerUnit_isUniformizingElement F)
    lam (torusSize lam) (torusSize_bounds lam)
  have hc' := integralOpen_isEntryBounded_zero F hc
  have hg := htorus.mul hc'
  rw [add_zero] at hg
  have hb := hC _ _ (matrix_isEntryBounded F h hr hg hx hy)
  calc
    _ ≤ C * B ^ (N + torusSize lam + torusSize lam) := hb
    _ = _ := by simp only [pow_add, mul_pow]; ring

end Langlands.RankinSelberg.TwoBlockDominantRectangular
