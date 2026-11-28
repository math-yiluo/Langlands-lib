import Langlands.Global.RankinSelberg.RealSlotCellMeasure
import Langlands.Global.RankinSelberg.RealSlotOuter
import Langlands.Global.RankinSelberg.RealGodementCanonicalCoefficient
import Langlands.Global.RankinSelberg.RealToralQuotientDensity
import Langlands.Global.RankinSelberg.RealGodementOpenCellConvergence
import Langlands.Global.RankinSelberg.RealEqualDualConvergence
import Langlands.Analysis.DominatedHolomorphicIntegral

/-! # The Levi-staged Jacquet integral of a slot set -/

noncomputable section

open MeasureTheory Matrix
open scoped NNReal ENNReal
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.RealLeviChartIntegrable Langlands.Archimedean.RealLeviTwoBlock
open Langlands.Archimedean.RealLeviBorel Langlands.Archimedean.RealLeviLeviBorel
open Langlands.Archimedean.RealLeviShear
open Langlands.Global.RankinSelbergGlobal.RealGodement
open Langlands.Global.RankinSelbergGlobal.RealGodementProfiles
open Langlands.Global.RankinSelbergGlobal.RealIwasawa
open Langlands.Whittaker (standardCharacter)

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

private local instance (d : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent d ℝ) :=
  borel _
private local instance (d : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent d ℝ) := ⟨rfl⟩

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Nu" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "w" => Langlands.GeneralLinear.weylLong (r + 1) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ

/-! ## The torus twist of the open cell -/

/-- The standard character twisted by the positive torus `torus y`. -/
def twistChar (a : ℝˣ) (y : Fin (r + 1) → ℝ) (u : Nu) : ℂ :=
  (standardCharacter (realScaledCharacter a) r (conjTorus y u) : ℂ)

theorem norm_twistChar (a : ℝˣ) (y : Fin (r + 1) → ℝ) (u : Nu) : ‖twistChar a y u‖ = 1 :=
  Langlands.Whittaker.norm_standardCharacter _ _ _

theorem continuous_twistChar (a : ℝˣ) (y : Fin (r + 1) → ℝ) : Continuous (twistChar a y) := by
  have h : Continuous fun u : Nu => (standardCharacter (realScaledCharacter a) r u : ℂ) := by
    have : (fun u : Nu => (standardCharacter (realScaledCharacter a) r u : ℂ)) =
        fun u => (realScaledCharacter a).complex (Multiplicative.toAdd
          (Langlands.GeneralLinear.UpperUnipotent.superdiagonalSumContinuous (n := r) (R := ℝ) u)) := by
      funext u
      rfl
    rw [this]
    exact (realScaledCharacter a).continuous_complex.comp (continuous_toAdd.comp
      (Langlands.GeneralLinear.UpperUnipotent.superdiagonalSumContinuous (n := r) (R := ℝ)).continuous)
  exact h.comp (continuous_conjTorus_right y)

theorem twistChar_mul (a : ℝˣ) (y : Fin (r + 1) → ℝ) (u v : Nu) :
    twistChar a y (u * v) = twistChar a y u * twistChar a y v := by
  have h : conjTorus y (u * v) = conjTorus y u * conjTorus y v := by
    apply Subtype.ext
    change torus y * (u.val * v.val) * torus (-y) =
      (torus y * u.val * torus (-y)) * (torus y * v.val * torus (-y))
    rw [torus_neg]
    group
  rw [twistChar, h, map_mul, Units.val_mul]
  rfl

theorem conjTorus_conjTorus_neg (y : Fin (r + 1) → ℝ) (u : Nu) :
    conjTorus y (conjTorus (-y) u) = u := by
  apply Subtype.ext
  change torus y * (torus (-y) * u.val * torus (-(-y))) * torus (-y) = u.val
  rw [neg_neg, torus_neg]
  group

theorem weyl_torus_conj (y : Fin (r + 1) → ℝ) (u : Nu) (g : G) :
    w * u.val * (torus y * g) =
      torus (fun i => y i.rev) * ((w * (conjTorus (-y) u).val) * g) := by
  have hw := Langlands.GeneralLinear.weylLong_mul_self (r + 1) ℝ
  rw [← RealEqualDualConvergence.weylLong_torus_weylLong]
  change _ = w * torus y * w * (w * (torus (-y) * u.val * torus (-(-y))) * g)
  have hww (h : G) : w * torus y * w * (w * h) = w * torus y * h := by
    rw [mul_assoc (w * torus y) w (w * h), ← mul_assoc w w h, hw, one_mul]
  rw [← mul_assoc (w * torus y * w) _ g, hww, neg_neg, torus_neg]
  group

/-- **The torus twist of the Jacquet integral.** In the chamber, the Jacquet integral at
`torus y · g` is the exponential factor of the torus times the modulus times the integral of
the section along `w N g` against the twisted character. -/
theorem additiveJacquetIntegral_torus_mul (a : ℝˣ) {p : Fin (r + 1) → Fin 2} {φ : U → ℂ}
    (hφ : IsCompactProfile p φ) {z : Fin (r + 1) → ℂ} (hz : z ∈ realSpectralChamber r)
    (y : Fin (r + 1) → ℝ) (g : G) :
    Integrable (fun v : Nu => standardSection z φ (w * v.val * g) * twistChar a y v)
        (upperStepHaar r a) ∧
      additiveJacquetIntegral a (standardSection z φ) (torus y * g) =
        Complex.exp (∑ i, shiftExp z i * (y i.rev : ℂ)) *
          (Real.exp (torusModularLog (r + 1) y) : ℂ) *
          ∫ v, standardSection z φ (w * v.val * g) * twistChar a y v ∂upperStepHaar r a := by
  have := upperStepHaar_isHaar r a
  set f := standardSection z φ
  set H : Nu → ℂ := fun v => f (w * v.val * g) * twistChar a y v
  set E := Complex.exp (∑ i, shiftExp z i * (y i.rev : ℂ))
  have hfc : Continuous f := continuous_standardSection hφ.1 z
  have hHc : Continuous H := by
    refine Continuous.mul (hfc.comp ?_) (continuous_twistChar a y)
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hK : additiveJacquetKernel a f (torus y * g) = fun u => E * H (conjTorus (-y) u) := by
    funext u
    rw [additiveJacquetKernel, weyl_torus_conj]
    have h1 := standardSection_unipotent_torus_mul hφ z (Subgroup.one_mem _) (fun i => y i.rev)
      (w * (conjTorus (-y) u).val * g)
    rw [one_mul] at h1
    change f _ = E * f _ at h1
    rw [h1]
    simp only [H, twistChar, conjTorus_conjTorus_neg]
    ring
  have hmap := map_conjTorus (upperStepHaar r a) (-y)
  have hc : ENNReal.ofReal (Real.exp (-torusModularLog (r + 1) (-y))) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact Real.exp_pos _
  have hm : Measurable (conjTorus (n := r + 1) (-y)) := (continuous_conjTorus_right (-y)).measurable
  have hKi : Integrable (additiveJacquetKernel a f (torus y * g)) (upperStepHaar r a) :=
    integrable_additiveJacquetKernel_of_mem_principalSeries a
      (RealStrictCharacterLanglandsQuotient.isSignedPower (characterList p z))
      (isStrictlyDominant_characterList p hz) (standardSection_mem hφ z).1.1 _
  have hE : E ≠ 0 := Complex.exp_ne_zero _
  have hHi : Integrable H (upperStepHaar r a) := by
    rw [hK] at hKi
    have h2 : Integrable (fun u => H (conjTorus (-y) u)) (upperStepHaar r a) := by
      have := hKi.const_mul E⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hE] using this
    have h3 : Integrable H ((upperStepHaar r a).map (conjTorus (-y))) :=
      (integrable_map_measure hHc.aestronglyMeasurable hm.aemeasurable).mpr h2
    rw [hmap] at h3
    exact (integrable_smul_measure hc ENNReal.ofReal_ne_top).mp h3
  refine ⟨hHi, ?_⟩
  rw [additiveJacquetIntegral, hK, integral_const_mul]
  have h4 : ∫ u, H (conjTorus (-y) u) ∂upperStepHaar r a =
      ∫ v, H v ∂((upperStepHaar r a).map (conjTorus (-y))) :=
    (integral_map hm.aemeasurable hHc.aestronglyMeasurable).symm
  rw [h4, hmap, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, map_neg, neg_neg,
    Complex.real_smul]
  ring

/-! ## The phase of the block coordinates -/

theorem cellPt_zero_entry {ι : Type*} [LinearOrder ι] {cl : Fin (r + 1) → ι} (hcl : Monotone cl)
    (Z : CoordM cl → ℝ) (i j : Fin (r + 1)) :
    ((cellPt hcl Z 0 : Nu) : G).val i j = lowerM cl Z i.rev j.rev := by
  have h := weylLong_mul_cellPt hcl Z 0
  rw [lowerCGL_zero, mul_one] at h
  calc ((cellPt hcl Z 0 : Nu) : G).val i j = (w * ((cellPt hcl Z 0 : Nu) : G)) i.rev j := by
        rw [Langlands.GeneralLinear.weylLong_mul_entry, Fin.rev_rev]
    _ = (lowerMGL cl Z * w) i.rev j := by rw [h]
    _ = lowerM cl Z i.rev j.rev := by
        rw [Langlands.GeneralLinear.mul_weylLong_entry, ← lowerMGL_val]

theorem conjTorus_entry (y : Fin (r + 1) → ℝ) (u : Nu) (i j : Fin (r + 1)) :
    ((conjTorus y u : Nu) : G).val i j = Real.exp (y i) * (u : G).val i j * Real.exp (-y j) := by
  change ((torus y * (u : G) * torus (-y) : G) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j = _
  rw [Units.val_mul, Units.val_mul, torus_val, torus_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp

theorem realScaledCharacter_complex (a : ℝˣ) (x : ℝ) :
    (realScaledCharacter a).complex x =
      Complex.exp (((2 * Real.pi * ((a : ℝ) * x) : ℝ) : ℂ) * Complex.I) := rfl

/-- Reindexing the superdiagonal by the slots: the superdiagonal entry `(i, i + 1)` lies over
the slot starting at `r - 1 - i`. -/
theorem sum_superdiag_slots (S : SlotSet (r + 1)) (F : S.starts → ℝ) :
    ∑ i : Fin r, (if h : r - 1 - (i : ℕ) ∈ S.starts then F ⟨r - 1 - i, h⟩ else 0) =
      ∑ q : S.starts, F q := by
  classical
  have hq : ∀ q : S.starts, r - 1 - (q : ℕ) < r := by
    intro q
    have := S.lt q q.2
    omega
  have h1 : ∀ q : S.starts, ∑ i : Fin r, (if i = ⟨r - 1 - q, hq q⟩ then F q else 0) = F q := by
    intro q
    rw [Finset.sum_ite_eq']
    simp
  rw [← Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : r - 1 - (i : ℕ) ∈ S.starts
  · rw [dite_eq_left h, Finset.sum_eq_single ⟨r - 1 - i, h⟩]
    · rw [ite_eq_left]
      apply Fin.ext
      simp only
      have := S.lt _ h
      omega
    · intro q _ hne
      rw [ite_eq_right]
      intro e
      apply hne
      apply Subtype.ext
      have := congrArg Fin.val e
      simp only at this
      have := S.lt q q.2
      show (q : ℕ) = r - 1 - i
      omega
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · rw [dite_eq_right h]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [ite_eq_right]
    intro e
    apply h
    have := congrArg Fin.val e
    simp only at this
    have h2 := S.lt q q.2
    have h3 : r - 1 - (i : ℕ) = q := by omega
    rw [h3]
    exact q.2

/-- The phases `a e^{y_{rev(p+1)} - y_{rev p}}` of the slot coordinates under the torus twist. -/
def slotPhase (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ) (p : ℕ) : ℝ :=
  if hp : p ∈ S.starts then
    (a : ℝ) * Real.exp (y (SlotSet.second hp).rev - y (SlotSet.first hp).rev)
  else 0

/-- On a slot `q`, the phase is `a e^{y_{rev(q+1)} - y_{rev q}}`. -/
theorem slotPhase_coe (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ) (q : S.starts) :
    slotPhase S a y q =
      (a : ℝ) * Real.exp (y (SlotSet.second q.2).rev - y (SlotSet.first q.2).rev) := by
  simp [slotPhase, q.2]

theorem sum_superdiag_cellPt_block (S : SlotSet (r + 1)) (y : Fin (r + 1) → ℝ)
    (Z : CoordM S.blockIdx → ℝ) :
    ∑ i : Fin r, ((conjTorus y (cellPt SlotSet.blockIdx_monotone Z 0) : Nu) : G).val
        i.castSucc i.succ =
      ∑ q : S.starts, Real.exp (y (SlotSet.second q.2).rev - y (SlotSet.first q.2).rev) *
        SlotSet.slotOfM Z q := by
  rw [← sum_superdiag_slots S (fun q => Real.exp (y (SlotSet.second q.2).rev -
    y (SlotSet.first q.2).rev) * SlotSet.slotOfM Z q)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTorus_entry, cellPt_zero_entry]
  have hi1 : ((i.castSucc).rev : ℕ) = r - i := by simp [Fin.val_rev]
  have hi2 : ((i.succ).rev : ℕ) = r - 1 - i := by simp [Fin.val_rev]; omega
  by_cases h : r - 1 - (i : ℕ) ∈ S.starts
  · rw [dite_eq_left h]
    have hs : (i.castSucc).rev = SlotSet.second h := Fin.ext (by
      rw [hi1]; simp only [SlotSet.second]; have := i.isLt; omega)
    have hf : (i.succ).rev = SlotSet.first h := Fin.ext (by rw [hi2]; simp [SlotSet.first])
    have hc : S.blockIdx (i.castSucc).rev = S.blockIdx (i.succ).rev ∧
        (i.succ).rev < (i.castSucc).rev := by
      rw [hs, hf]
      exact ⟨SlotSet.blockIdx_second h, by
        change r - 1 - (i : ℕ) < r - 1 - (i : ℕ) + 1; omega⟩
    simp only [lowerM, Matrix.of_apply, dite_eq_left hc]
    have hy1 : y i.castSucc = y (SlotSet.second h).rev := by rw [← hs, Fin.rev_rev]
    have hy2 : y i.succ = y (SlotSet.first h).rev := by rw [← hf, Fin.rev_rev]
    rw [hy1, hy2]
    have hZ : Z ⟨((i.castSucc).rev, (i.succ).rev), hc⟩ = SlotSet.slotOfM Z ⟨r - 1 - i, h⟩ := by
      simp only [SlotSet.slotOfM]
      congr 1
      apply Subtype.ext
      rw [SlotSet.coordMEquiv_symm_val]
      exact Prod.ext hs hf
    rw [hZ, sub_eq_add_neg, Real.exp_add]
    ring
  · rw [dite_eq_right h]
    have hn : ¬ (S.blockIdx (i.castSucc).rev = S.blockIdx (i.succ).rev ∧
        (i.succ).rev < (i.castSucc).rev) := by
      rintro ⟨he, hlt⟩
      have := SlotSet.eq_of_blockIdx_eq hlt he
      rw [hi2] at this
      exact h this.1
    have hne : (i.castSucc).rev ≠ (i.succ).rev := fun e => by
      have := congrArg Fin.val e
      rw [hi1, hi2] at this
      omega
    simp only [lowerM, Matrix.of_apply, dite_eq_right hn, ite_eq_right hne]
    ring

/-- **The twisted character on the block coordinates** is the exponential of the slot phases
times the slot coordinates. -/
theorem twistChar_cellPt_block (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ)
    (Z : CoordM S.blockIdx → ℝ) :
    twistChar a y (cellPt SlotSet.blockIdx_monotone Z 0) =
      Complex.exp (((2 * Real.pi * ∑ q : S.starts, slotPhase S a y q * SlotSet.slotOfM Z q : ℝ) : ℂ) *
        Complex.I) := by
  rw [twistChar, Langlands.Whittaker.standardCharacter_apply]
  change (realScaledCharacter a).complex (∑ i : Fin r,
    ((conjTorus y (cellPt SlotSet.blockIdx_monotone Z 0) : Nu) : G).val i.castSucc i.succ) = _
  rw [realScaledCharacter_complex, sum_superdiag_cellPt_block, Finset.mul_sum]
  congr 4
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [slotPhase_coe]
  ring

/-! ## The open cell integral in Levi stages -/

/-- **The inner integral over the block coordinates** of the twisted open cell integrand is the
twisted character at the opposite radical point times the inner Levi integral with the slot
phases. -/
theorem integral_cellPt_block (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ)
    (f : G → ℂ) (g : G) (X : CoordC S.blockIdx → ℝ) :
    ∫ Z, f (w * ((cellPt SlotSet.blockIdx_monotone Z X : Nu) : G) * g) *
        twistChar a y (cellPt SlotSet.blockIdx_monotone Z X) =
      twistChar a y (cellPt SlotSet.blockIdx_monotone 0 X) *
        leviIntegral S f (slotPhase S a y)
          (S.swapGL * lowerCGL SlotSet.blockIdx_monotone X * w * g) := by
  rw [leviIntegral, ← integral_const_mul,
    ← SlotSet.integral_comp_slotOfM (S := S) (fun x => twistChar a y (cellPt SlotSet.blockIdx_monotone 0 X) *
      (f (S.swapGL * S.unip (S.ext x) *
        (S.swapGL * lowerCGL SlotSet.blockIdx_monotone X * w * g)) *
      Complex.exp (((2 * Real.pi * ∑ q : S.starts, slotPhase S a y q * x q : ℝ) : ℂ) *
        Complex.I)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only
  have h1 : w * ((cellPt SlotSet.blockIdx_monotone Z X : Nu) : G) * g =
      S.swapGL * S.unip (S.ext (SlotSet.slotOfM Z)) *
        (S.swapGL * lowerCGL SlotSet.blockIdx_monotone X * w * g) := by
    rw [weylLong_mul_cellPt, SlotSet.lowerMGL_eq]
    simp only [mul_assoc]
  have h2 : twistChar a y (cellPt SlotSet.blockIdx_monotone Z X) =
      Complex.exp (((2 * Real.pi * ∑ q : S.starts, slotPhase S a y q * SlotSet.slotOfM Z q : ℝ) :
        ℂ) * Complex.I) * twistChar a y (cellPt SlotSet.blockIdx_monotone 0 X) := by
    rw [cellPt_mul, twistChar_mul, twistChar_cellPt_block]
  rw [h1, h2]
  ring

theorem continuous_cell_integrand (a : ℝˣ) (y : Fin (r + 1) → ℝ) {f : G → ℂ} (hf : Continuous f)
    (g : G) : Continuous fun v : Nu => f (w * v.val * g) * twistChar a y v := by
  refine Continuous.mul (hf.comp ?_) (continuous_twistChar a y)
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

/-- **The open cell integral in Levi stages.** If the twisted open cell integrand of a
continuous function is integrable, then the outer integrand over the opposite radical coordinates
`X` (the twisted character at `X` times the inner Levi integral with the slot phases) is
integrable, and the open cell integral is `haarScale r a` times its integral. -/
theorem integral_cell_eq_levi (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ)
    {f : G → ℂ} (hf : Continuous f) (g : G)
    (hI : Integrable (fun v : Nu => f (w * v.val * g) * twistChar a y v) (upperStepHaar r a)) :
    Integrable (fun X : CoordC S.blockIdx → ℝ =>
        twistChar a y (cellPt SlotSet.blockIdx_monotone 0 X) *
          leviIntegral S f (slotPhase S a y)
            (S.swapGL * lowerCGL SlotSet.blockIdx_monotone X * w * g)) ∧
    ∫ v, f (w * v.val * g) * twistChar a y v ∂upperStepHaar r a =
      (haarScale r a : ℝ) * ∫ X : CoordC S.blockIdx → ℝ,
        twistChar a y (cellPt SlotSet.blockIdx_monotone 0 X) *
          leviIntegral S f (slotPhase S a y)
            (S.swapGL * lowerCGL SlotSet.blockIdx_monotone X * w * g) := by
  obtain ⟨hprod, heq⟩ :=
    integral_upperStepHaar_eq SlotSet.blockIdx_monotone a (continuous_cell_integrand a y hf g) hI
  have hin := funext fun X => integral_cellPt_block S a y f g X
  refine ⟨?_, ?_⟩
  · have := hprod.integral_prod_right
    simp only at this
    rwa [hin] at this
  · rw [heq, hin]

/-! ## The deformation of the exponents along the block index -/

theorem standardSection_sub_smul (φ : U → ℂ) (z : Fin (r + 1) → ℂ) (μ : Fin (r + 1) → ℝ)
    (t : ℂ) (g : G) :
    standardSection (fun i => z i - t * μ i) φ g =
      Complex.exp (-t * ∑ i, (μ i : ℂ) * (RealIwasawa.alpha g i : ℂ)) * standardSection z φ g := by
  rw [standardSection_eq, standardSection_eq, ← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sum_mul_alpha_swapGL_unip_mul (S : SlotSet (r + 1)) {μ : Fin (r + 1) → ℝ}
    (hμ : ∀ j, μ (S.perm j) = μ j) (x : ℕ → ℝ) (g : G) :
    ∑ i, μ i * RealIwasawa.alpha (S.swapGL * S.unip x * g) i = ∑ i, μ i * RealIwasawa.alpha g i := by
  rw [SlotSet.alpha_swapGL_unip_mul]
  exact SlotSet.sum_mul_perm_add_cellExponent hμ _ _

/-- **The deformation of the inner Levi integral.** Moving the exponents along a weight that is
constant on the slots multiplies the inner Levi integral by an exponential of the Iwasawa
coordinates of the outer point. -/
theorem leviIntegral_sub_smul (S : SlotSet (r + 1)) (φ : U → ℂ) (z : Fin (r + 1) → ℂ)
    {μ : Fin (r + 1) → ℝ} (hμ : ∀ j, μ (S.perm j) = μ j) (t : ℂ) (b : ℕ → ℝ) (g : G) :
    leviIntegral S (standardSection (fun i => z i - t * μ i) φ) b g =
      Complex.exp (-t * ((∑ i, μ i * RealIwasawa.alpha g i : ℝ) : ℂ)) *
        leviIntegral S (standardSection z φ) b g := by
  rw [leviIntegral, leviIntegral, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [standardSection_sub_smul, ← sum_mul_alpha_swapGL_unip_mul S hμ (S.ext x) g]
  push_cast
  ring

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
