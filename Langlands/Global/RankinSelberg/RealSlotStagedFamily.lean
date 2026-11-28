import Langlands.Global.RankinSelberg.RealSlotStaged

/-! # The Levi-staged Jacquet family along the block deformation -/

noncomputable section

open MeasureTheory Matrix Filter Set Metric
open scoped NNReal ENNReal Topology
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.RealLeviChartIntegrable Langlands.Archimedean.RealLeviTwoBlock
open Langlands.Archimedean.RealLeviBorel Langlands.Archimedean.RealLeviLeviBorel
open Langlands.Archimedean.RealLeviShear
open Langlands.Global.RankinSelbergGlobal.RealGodement
open Langlands.Global.RankinSelbergGlobal.RealGodementProfiles
open Langlands.Global.RankinSelbergGlobal.RealIwasawa

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
local notation "K" => unitaryCompact ℝ (r + 1)

/-! ## Continuity in the opposite radical chart -/

theorem continuous_GL_of_val {X : Type*} [TopologicalSpace X] {N : ℕ}
    {f : X → Langlands.GeneralLinear N ℝ}
    (hf : Continuous fun x => ((f x : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)) :
    Continuous f := by
  rw [Units.continuous_iff]
  refine ⟨hf, ?_⟩
  have h : (fun x => (((f x)⁻¹ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)) =
      fun x => ((f x : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)⁻¹ := by
    funext x
    exact Matrix.coe_units_inv (f x)
  rw [h]
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine (continuousAt_matrix_inv _ ?_).comp hf.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det _).mp (f x).isUnit).ne_zero

theorem continuous_lowerCGL {ι : Type*} [LinearOrder ι] {N : ℕ} {cl : Fin N → ι}
    (hcl : Monotone cl) : Continuous (lowerCGL hcl) := by
  refine continuous_GL_of_val ?_
  have h : (fun X => ((lowerCGL hcl X : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)) =
      lowerC cl := funext fun X => lowerCGL_val hcl X
  rw [h]
  exact continuous_lowerC

theorem weylLong_mem : w ∈ K := by
  show ((Langlands.GeneralLinear.weylLong (r + 1) ℝ : G) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) ∈
    Matrix.unitaryGroup (Fin (r + 1)) ℝ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  have h := congrArg Units.val (Langlands.GeneralLinear.inverseTranspose_weylLong (r + 1) ℝ)
  rw [Langlands.GeneralLinear.inverseTranspose_coe, Langlands.GeneralLinear.weylLong_inv] at h
  rw [h, ← Units.val_mul, Langlands.GeneralLinear.weylLong_mul_self, Units.val_one]

/-! ## The block deformation -/

/-- The block index as a real weight. -/
def blockWeight (S : SlotSet (r + 1)) (i : Fin (r + 1)) : ℝ := S.blockIdx i

theorem blockWeight_perm (S : SlotSet (r + 1)) (j : Fin (r + 1)) :
    blockWeight S (S.perm j) = blockWeight S j := by
  rw [blockWeight, blockWeight, SlotSet.blockIdx_perm]

/-- The exponents moved by `t` along the block index. -/
def deform (S : SlotSet (r + 1)) (z : Fin (r + 1) → ℂ) (t : ℂ) (i : Fin (r + 1)) : ℂ :=
  z i - t * (blockWeight S i : ℂ)

theorem deform_re (S : SlotSet (r + 1)) (z : Fin (r + 1) → ℂ) (t : ℂ) (i : Fin (r + 1)) :
    (deform S z t i).re = (z i).re - t.re * blockWeight S i := by
  simp [deform, Complex.mul_re]

theorem deform_zero (S : SlotSet (r + 1)) (z : Fin (r + 1) → ℂ) : deform S z 0 = z := by
  funext i
  simp [deform]

theorem differentiable_deform (S : SlotSet (r + 1)) (z : Fin (r + 1) → ℂ) :
    Differentiable ℂ (deform S z) :=
  differentiable_pi.mpr fun i =>
    (differentiable_const (c := z i)).sub (differentiable_id.mul_const _)

theorem deform_slot (S : SlotSet (r + 1)) (m : ℕ → ℕ) {z : Fin (r + 1) → ℂ}
    (hz : ∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q) (t : ℂ) :
    ∀ q (hq : q ∈ S.starts),
      deform S z t (SlotSet.first hq) - deform S z t (SlotSet.second hq) = m q := by
  intro q hq
  have h := SlotSet.blockIdx_second hq
  simp only [deform, blockWeight, h]
  rw [← hz q hq]
  ring

/-- The half-weights `±m/2` on the slots. -/
def halfWeights (S : SlotSet (r + 1)) (m : ℕ → ℕ) : Fin (r + 1) → ℝ :=
  S.slotVec (fun q => (m q : ℝ) / 2) (fun q => -((m q : ℝ) / 2))

theorem abs_halfWeights_le (S : SlotSet (r + 1)) (m : ℕ → ℕ) (i : Fin (r + 1)) :
    |halfWeights S m i| ≤ (∑ q ∈ S.starts, (m q : ℝ)) / 2 := by
  have hT : ∀ q ∈ S.starts, (m q : ℝ) ≤ ∑ q ∈ S.starts, (m q : ℝ) := fun q hq =>
    Finset.single_le_sum (f := fun q => (m q : ℝ)) (fun _ _ => Nat.cast_nonneg _) hq
  have h0 : 0 ≤ ∑ q ∈ S.starts, (m q : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  simp only [halfWeights, SlotSet.slotVec]
  split_ifs with h1 h2
  · rw [abs_of_nonneg (by positivity)]
    linarith [hT _ h1]
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    linarith [hT _ h2.2]
  · simp only [abs_zero]
    linarith

/-- **The deformed exponents are strictly dominant far to the right.** -/
theorem deform_mem_chamber (S : SlotSet (r + 1)) (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0)
    {z : Fin (r + 1) → ℂ} (hre : ∀ i, (z i).re = halfWeights S m i) {t : ℂ}
    (ht : ∑ q ∈ S.starts, (m q : ℝ) < t.re) : deform S z t ∈ realSpectralChamber r := by
  intro i
  rw [deform_re, deform_re, hre, hre]
  have h0 : 0 ≤ ∑ q ∈ S.starts, (m q : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  by_cases hi : (i : ℕ) ∈ S.starts
  · have hf : i.castSucc = SlotSet.first hi := Fin.ext rfl
    have hs : i.succ = SlotSet.second hi := Fin.ext rfl
    rw [hf, hs]
    have hb : blockWeight S (SlotSet.second hi) = blockWeight S (SlotSet.first hi) := by
      simp [blockWeight, SlotSet.blockIdx_second hi]
    rw [hb, halfWeights, SlotSet.slotVec_of_inSlot _ _ (SlotSet.inSlot_first hi),
      SlotSet.slotVec_of_inSlot _ _ (SlotSet.inSlot_second hi)]
    simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    have : (0 : ℝ) < m i := by exact_mod_cast Nat.pos_of_ne_zero (hm _ hi)
    linarith
  · have hlt : S.blockIdx i.castSucc < S.blockIdx i.succ :=
      SlotSet.blockIdx_lt_of_lt (Fin.castSucc_lt_succ (i := i)) (fun h => hi h.1)
    have hlt' : blockWeight S i.castSucc + 1 ≤ blockWeight S i.succ := by
      simp only [blockWeight]
      exact_mod_cast hlt
    have h1 := abs_halfWeights_le S m i.castSucc
    have h2 := abs_halfWeights_le S m i.succ
    have htr : 0 ≤ t.re := by linarith
    have h3 : t.re * (blockWeight S i.castSucc + 1) ≤ t.re * blockWeight S i.succ :=
      mul_le_mul_of_nonneg_left hlt' htr
    have h4 := (abs_le.mp h1).1
    have h5 := (abs_le.mp h2).2
    nlinarith

/-! ## The spherical majorant of the deformed inner integrals -/

/-- The exponent `-s μ + ρ` of the spherical majorant. -/
def sphExp (S : SlotSet (r + 1)) (s : ℝ) (i : Fin (r + 1)) : ℝ :=
  -s * blockWeight S i + rhoShift i

/-- **Uniform bound of the deformed inner Levi integrals.** -/
theorem norm_leviIntegral_deform_le (S : SlotSet (r + 1)) {p : Fin (r + 1) → Fin 2}
    {φ : U → ℂ} (hφ : IsCompactProfile p φ) (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0)
    {z : Fin (r + 1) → ℂ}
    (hz : ∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q)
    (hre : ∀ i, (z i).re = halfWeights S m i)
    (hmodes : SlotModes (slotsOf S m) (standardSection z φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℂ) (b : ℕ → ℝ) (g : G),
      ‖leviIntegral S (standardSection (deform S z t) φ) b g‖ ≤
        C * (∏ q : S.starts, |b q| ^ ((m q : ℝ) / 2)) * spherical (sphExp S t.re) g := by
  obtain ⟨C, hC, h⟩ := norm_leviIntegral_le_spherical S hφ m hm z hmodes
  refine ⟨C, hC, fun t b g => ?_⟩
  have hb := h (deform S z t) (deform_slot S m hz t) b g
  have he : ∀ i, blockRe S m (deform S z t) i + rhoShift i = sphExp S t.re i := by
    intro i
    simp only [blockRe, deform_re, hre, sphExp, halfWeights]
    ring
  simp only [he] at hb
  exact hb

theorem spherical_sphExp_le (S : SlotSet (r + 1)) {s₁ s₂ s : ℝ} (h₁ : s₁ ≤ s) (h₂ : s ≤ s₂)
    (g : G) :
    spherical (sphExp S s) g ≤ spherical (sphExp S s₁) g + spherical (sphExp S s₂) g := by
  set Λ := ∑ i, blockWeight S i * RealIwasawa.alpha g i
  set ρ := ∑ i, rhoShift i * RealIwasawa.alpha g i
  have hs : ∀ u, spherical (sphExp S u) g = Real.exp (ρ - u * Λ) := by
    intro u
    simp only [spherical, sphExp, ρ, Λ]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hs, hs, hs]
  rcases le_total 0 Λ with hΛ | hΛ
  · have : Real.exp (ρ - s * Λ) ≤ Real.exp (ρ - s₁ * Λ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (ρ - s₂ * Λ)]
  · have : Real.exp (ρ - s * Λ) ≤ Real.exp (ρ - s₂ * Λ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (ρ - s₁ * Λ)]

/-- The outer point `w_M n̄(X) w g` of the opposite radical chart. -/
def outerPt (S : SlotSet (r + 1)) (X : CoordC S.blockIdx → ℝ) (g : G) : G :=
  S.swapGL * lowerCGL SlotSet.blockIdx_monotone X * w * g

theorem continuous_outerPt (S : SlotSet (r + 1)) (g : G) : Continuous fun X => outerPt S X g :=
  ((continuous_const.mul (continuous_lowerCGL _)).mul continuous_const).mul continuous_const

theorem spherical_outerPt (S : SlotSet (r + 1)) (c : Fin (r + 1) → ℝ) (X : CoordC S.blockIdx → ℝ)
    {g : G} (hg : g ∈ K) :
    spherical c (outerPt S X g) = spherical c
      (lowerCGL SlotSet.blockIdx_monotone (X ∘ permCoord S.perm SlotSet.blockIdx_perm)) := by
  have hwg : w * g ∈ K := mul_mem weylLong_mem hg
  calc spherical c (outerPt S X g)
      = spherical c (S.swapGL * lowerCGL SlotSet.blockIdx_monotone X * (w * g)) := by
        rw [outerPt, mul_assoc _ w g]
    _ = spherical c (S.swapGL * lowerCGL SlotSet.blockIdx_monotone X) :=
        spherical_mul_unitary c _ ⟨w * g, hwg⟩
    _ = spherical c (lowerCGL SlotSet.blockIdx_monotone (X ∘ permCoord S.perm SlotSet.blockIdx_perm) *
          S.swapGL) := by
        rw [SlotSet.swapGL_eq_permutation, permutation_mul_lowerCGL]
    _ = _ := spherical_mul_unitary c _ ⟨S.swapGL, S.swapGL_mem⟩

theorem integrable_spherical_sphExp (S : SlotSet (r + 1)) {s : ℝ} (hs : 0 < s) :
    Integrable fun X : CoordC S.blockIdx → ℝ =>
      spherical (sphExp S s) (lowerCGL SlotSet.blockIdx_monotone X) := by
  refine integrable_spherical_lowerCGL SlotSet.blockIdx_monotone (sphExp S s) ?_ ?_
  · intro k l hkl
    have hle : blockWeight S k ≤ blockWeight S l := by
      simp only [blockWeight]
      exact_mod_cast SlotSet.blockIdx_le_of_le (Fin.le_def.mpr (by omega))
    simp only [sphExp, rhoShift]
    have : ((l : ℕ) : ℝ) = (k : ℕ) + 1 := by exact_mod_cast hkl.symm
    rw [this]
    nlinarith
  · intro k l hkl hlt
    have hlt' : blockWeight S k < blockWeight S l := by
      simp only [blockWeight]
      exact_mod_cast hlt
    simp only [sphExp, rhoShift]
    have : ((l : ℕ) : ℝ) = (k : ℕ) + 1 := by exact_mod_cast hkl.symm
    rw [this]
    nlinarith

theorem integrable_spherical_outerPt (S : SlotSet (r + 1)) {s : ℝ} (hs : 0 < s) {g : G}
    (hg : g ∈ K) :
    Integrable fun X : CoordC S.blockIdx → ℝ => spherical (sphExp S s) (outerPt S X g) := by
  simp_rw [spherical_outerPt S _ _ hg]
  exact (measurePreserving_comp_permCoord S.perm SlotSet.blockIdx_perm).integrable_comp_of_integrable
    (integrable_spherical_sphExp S hs)

theorem integral_spherical_outerPt (S : SlotSet (r + 1)) (s : ℝ) {g : G} (hg : g ∈ K) :
    ∫ X : CoordC S.blockIdx → ℝ, spherical (sphExp S s) (outerPt S X g) =
      ∫ X : CoordC S.blockIdx → ℝ, spherical (sphExp S s) (lowerCGL SlotSet.blockIdx_monotone X) := by
  simp_rw [spherical_outerPt S _ _ hg]
  exact integral_comp_permCoord S.perm SlotSet.blockIdx_perm
    (fun X => spherical (sphExp S s) (lowerCGL SlotSet.blockIdx_monotone X))

/-! ## The staged integral -/

/-- The weight `Σ_i μ_i α_i` of the outer point. -/
def outerWeight (S : SlotSet (r + 1)) (g : G) (X : CoordC S.blockIdx → ℝ) : ℝ :=
  ∑ i, blockWeight S i * RealIwasawa.alpha (outerPt S X g) i

theorem continuous_outerWeight (S : SlotSet (r + 1)) (g : G) : Continuous (outerWeight S g) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul
    ((continuous_apply i).comp (RealIwasawa.continuous_alpha.comp (continuous_outerPt S g)))

/-- The staged integrand: the twisted character on the opposite radical point times the
deformed inner Levi integral at the outer point. -/
def stagedIntegrand (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ) (φ : U → ℂ)
    (z : Fin (r + 1) → ℂ) (g : G) (t : ℂ) (X : CoordC S.blockIdx → ℝ) : ℂ :=
  twistChar a y (cellPt SlotSet.blockIdx_monotone 0 X) *
    leviIntegral S (standardSection (deform S z t) φ) (slotPhase S a y) (outerPt S X g)

/-- The staged integral over the opposite radical. -/
def stagedIntegral (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ) (φ : U → ℂ)
    (z : Fin (r + 1) → ℂ) (g : G) (t : ℂ) : ℂ :=
  ∫ X, stagedIntegrand S a y φ z g t X

theorem stagedIntegrand_eq_exp (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ) (φ : U → ℂ)
    (z : Fin (r + 1) → ℂ) (g : G) (t : ℂ) (X : CoordC S.blockIdx → ℝ) :
    stagedIntegrand S a y φ z g t X =
      Complex.exp (-t * (outerWeight S g X : ℂ)) * stagedIntegrand S a y φ z g 0 X := by
  simp only [stagedIntegrand, deform_zero]
  rw [show deform S z t = fun i => z i - t * (blockWeight S i : ℂ) from rfl,
    leviIntegral_sub_smul S φ z (blockWeight_perm S)]
  simp only [outerWeight]
  ring

/-- **The staged formula in the chamber.** If the deformed exponents lie in the chamber, the
staged integrand is integrable and the deformed Jacquet family at `torus y · g` is the torus factor
of the shifted exponents times the modulus times `haarScale r a` times the staged integral. -/
theorem stagedIntegral_of_chamber (S : SlotSet (r + 1)) (a : ℝˣ) {p : Fin (r + 1) → Fin 2}
    {φ : U → ℂ} (hφ : IsCompactProfile p φ) (z : Fin (r + 1) → ℂ) {t : ℂ}
    (ht : deform S z t ∈ realSpectralChamber r) (y : Fin (r + 1) → ℝ) (g : G) :
    Integrable (stagedIntegrand S a y φ z g t) ∧
      canonicalJacquetFamily a hφ (deform S z t) (torus y * g) =
        Complex.exp (∑ i, shiftExp (deform S z t) i * (y i.rev : ℂ)) *
          (Real.exp (torusModularLog (r + 1) y) : ℂ) *
          ((haarScale r a : ℝ) * stagedIntegral S a y φ z g t) := by
  obtain ⟨hI, hJ⟩ := additiveJacquetIntegral_torus_mul a hφ ht y g
  obtain ⟨hI', hJ'⟩ := integral_cell_eq_levi S a y (continuous_standardSection hφ.1 _) g hI
  refine ⟨hI', ?_⟩
  rw [canonicalJacquetFamily_agrees a hφ ht, hJ, hJ']
  rfl

/-- **Holomorphy of the staged integral.** For a fixed point of the orthogonal group, the
staged integrand is integrable on the right half plane and the staged integral is holomorphic
there. The proof dominates the integrand locally in `t` by the spherical majorant. -/
theorem stagedIntegral_holomorphic (S : SlotSet (r + 1)) {p : Fin (r + 1) → Fin 2}
    {φ : U → ℂ} (hφ : IsCompactProfile p φ) (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0)
    {z : Fin (r + 1) → ℂ}
    (hz : ∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q)
    (hre : ∀ i, (z i).re = halfWeights S m i)
    (hmodes : SlotModes (slotsOf S m) (standardSection z φ)) (a : ℝˣ) (y : Fin (r + 1) → ℝ)
    {g : G} (hg : g ∈ K) :
    (∀ t : ℂ, t ∈ {t : ℂ | 0 < t.re} → Integrable (stagedIntegrand S a y φ z g t)) ∧
      DifferentiableOn ℂ (stagedIntegral S a y φ z g) {t : ℂ | 0 < t.re} := by
  obtain ⟨C, hC, hbound⟩ := norm_leviIntegral_deform_le S hφ m hm hz hre hmodes
  set P := ∏ q : S.starts, |slotPhase S a y q| ^ ((m q : ℝ) / 2) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun q _ => Real.rpow_nonneg (abs_nonneg _) _
  set T := ∑ q ∈ S.starts, (m q : ℝ)
  set t₁ : ℂ := ((T + 1 : ℝ) : ℂ)
  have ht₁ : deform S z t₁ ∈ realSpectralChamber r :=
    deform_mem_chamber S m hm hre (by simp only [t₁, Complex.ofReal_re]; linarith)
  have hI₁ := (stagedIntegral_of_chamber S a hφ z ht₁ y g).1
  set F := stagedIntegrand S a y φ z g
  have hΛ := continuous_outerWeight S g
  have hcexp : ∀ c : ℂ, Continuous fun X => Complex.exp (c * (outerWeight S g X : ℂ)) :=
    fun c => (continuous_const.mul (Complex.continuous_ofReal.comp hΛ)).cexp
  have h0 : F 0 = fun X => Complex.exp (t₁ * (outerWeight S g X : ℂ)) * F t₁ X := by
    funext X
    show _ = _ * stagedIntegrand S a y φ z g t₁ X
    rw [stagedIntegrand_eq_exp S a y φ z g t₁ X, ← mul_assoc, ← Complex.exp_add]
    simp
    rfl
  have h0meas : AEStronglyMeasurable (F 0) volume := by
    rw [h0]
    exact (hcexp t₁).aestronglyMeasurable.mul hI₁.aestronglyMeasurable
  have hmeas : ∀ t, AEStronglyMeasurable (F t) volume := by
    intro t
    have : F t = fun X => Complex.exp (-t * (outerWeight S g X : ℂ)) * F 0 X :=
      funext fun X => stagedIntegrand_eq_exp S a y φ z g t X
    rw [this]
    exact (hcexp (-t)).aestronglyMeasurable.mul h0meas
  have hnorm : ∀ t X, ‖F t X‖ ≤ C * P * spherical (sphExp S t.re) (outerPt S X g) := by
    intro t X
    simp only [F, stagedIntegrand, norm_mul, norm_twistChar, one_mul]
    exact hbound t _ _
  refine Langlands.Analysis.dominatedHolomorphicIntegral volume {t : ℂ | 0 < t.re} F hmeas ?_ ?_
  · refine Eventually.of_forall fun X => ?_
    have : (fun t => F t X) = fun t => Complex.exp (-t * (outerWeight S g X : ℂ)) * F 0 X :=
      funext fun t => stagedIntegrand_eq_exp S a y φ z g t X
    rw [this]
    exact ((differentiable_id.neg.mul_const _).cexp.mul_const _).differentiableOn
  · intro t₀ ht₀
    have ht₀' : 0 < t₀.re := ht₀
    have hball : ∀ t ∈ ball t₀ (2 * (t₀.re / 4)), t₀.re / 2 ≤ t.re ∧ t.re ≤ 2 * t₀.re := by
      intro t ht
      rw [mem_ball, dist_eq_norm] at ht
      have h := Complex.abs_re_le_norm (t - t₀)
      rw [Complex.sub_re] at h
      constructor <;> linarith [abs_le.mp (h.trans ht.le)]
    refine ⟨t₀.re / 4, by positivity, fun t ht => ?_, ?_⟩
    · have := (hball t ht).1
      show 0 < t.re
      linarith
    · refine ⟨fun X => C * P * (spherical (sphExp S (t₀.re / 2)) (outerPt S X g) +
        spherical (sphExp S (2 * t₀.re)) (outerPt S X g)), ?_, ?_⟩
      · exact ((integrable_spherical_outerPt S (by positivity) hg).add
          (integrable_spherical_outerPt S (by positivity) hg)).const_mul _
      · refine Eventually.of_forall fun X t ht => (hnorm t X).trans ?_
        exact mul_le_mul_of_nonneg_left
          (spherical_sphExp_le S (hball t ht).1 (hball t ht).2 _) (mul_nonneg hC hP0)

theorem norm_stagedIntegrand_le (S : SlotSet (r + 1)) {p : Fin (r + 1) → Fin 2}
    {φ : U → ℂ} (hφ : IsCompactProfile p φ) (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0)
    {z : Fin (r + 1) → ℂ}
    (hz : ∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q)
    (hre : ∀ i, (z i).re = halfWeights S m i)
    (hmodes : SlotModes (slotsOf S m) (standardSection z φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝˣ) (y : Fin (r + 1) → ℝ) (g : G) (t : ℂ) (X : CoordC S.blockIdx → ℝ),
      ‖stagedIntegrand S a y φ z g t X‖ ≤
        C * (∏ q : S.starts, |slotPhase S a y q| ^ ((m q : ℝ) / 2)) *
          spherical (sphExp S t.re) (outerPt S X g) := by
  obtain ⟨C, hC, hbound⟩ := norm_leviIntegral_deform_le S hφ m hm hz hre hmodes
  refine ⟨C, hC, fun a y g t X => ?_⟩
  simp only [stagedIntegrand, norm_mul, norm_twistChar, one_mul]
  exact hbound t _ _

/-- The right side of the staged formula for the Jacquet family. -/
def stagedFamily (S : SlotSet (r + 1)) (a : ℝˣ) (y : Fin (r + 1) → ℝ) (φ : U → ℂ)
    (z : Fin (r + 1) → ℂ) (g : G) (t : ℂ) : ℂ :=
  Complex.exp (∑ i, shiftExp (deform S z t) i * (y i.rev : ℂ)) *
    (Real.exp (torusModularLog (r + 1) y) : ℂ) * ((haarScale r a : ℝ) * stagedIntegral S a y φ z g t)

/-- **The staged formula on the right half plane.** By holomorphic continuation from the
chamber, the deformed Jacquet family equals `stagedFamily`, the staged integral multiplied by the
torus factor of the shifted exponents, the modulus and `haarScale r a`, for every deformation
parameter of positive real part. -/
theorem canonical_eq_stagedFamily (S : SlotSet (r + 1)) {p : Fin (r + 1) → Fin 2}
    {φ : U → ℂ} (hφ : IsCompactProfile p φ) (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0)
    {z : Fin (r + 1) → ℂ}
    (hz : ∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q)
    (hre : ∀ i, (z i).re = halfWeights S m i)
    (hmodes : SlotModes (slotsOf S m) (standardSection z φ)) (a : ℝˣ) (y : Fin (r + 1) → ℝ)
    {g : G} (hg : g ∈ K) {t : ℂ} (ht : 0 < t.re) :
    canonicalJacquetFamily a hφ (deform S z t) (torus y * g) = stagedFamily S a y φ z g t := by
  set V : Set ℂ := {t : ℂ | 0 < t.re}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hW := canonicalJacquetFamily_properties a hφ
  have hF1 : DifferentiableOn ℂ
      (fun t => canonicalJacquetFamily a hφ (deform S z t) (torus y * g)) V :=
    ((hW.2.2.1 [] (torus y * g)).comp (differentiable_deform S z)).differentiableOn
  have hsh : Differentiable ℂ fun t : ℂ => ∑ i, shiftExp (deform S z t) i * (y i.rev : ℂ) := by
    simp only [shiftExp, deform]
    fun_prop
  have hF2 : DifferentiableOn ℂ (stagedFamily S a y φ z g) V :=
    ((hsh.cexp.mul_const _).differentiableOn).mul
      ((stagedIntegral_holomorphic S hφ m hm hz hre hmodes a y hg).2.const_mul _)
  set T := ∑ q ∈ S.starts, (m q : ℝ)
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hev : (fun t => canonicalJacquetFamily a hφ (deform S z t) (torus y * g)) =ᶠ[𝓝 ((T + 1 : ℝ) : ℂ)]
      stagedFamily S a y φ z g := by
    have hO : IsOpen {t : ℂ | T < t.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hO.mem_nhds (by show T < (((T + 1 : ℝ) : ℂ)).re; simp only [Complex.ofReal_re]; linarith)]
      with t ht
    exact (stagedIntegral_of_chamber S a hφ z (deform_mem_chamber S m hm hre ht) y g).2
  exact (hF1.analyticOnNhd hV).eqOn_of_preconnected_of_eventuallyEq (hF2.analyticOnNhd hV)
    (convex_halfSpace_re_gt 0).isPreconnected
    (by show 0 < (((T + 1 : ℝ) : ℂ)).re; simp only [Complex.ofReal_re]; linarith) hev ht

/-! ## The bound on vertical lines -/

theorem prod_slotPhase (S : SlotSet (r + 1)) (m : ℕ → ℕ) (a : ℝˣ) (y : Fin (r + 1) → ℝ) :
    ∏ q : S.starts, |slotPhase S a y q| ^ ((m q : ℝ) / 2) =
      (∏ q : S.starts, |(a : ℝ)| ^ ((m q : ℝ) / 2)) *
        Real.exp (∑ q : S.starts, (m q : ℝ) / 2 *
          (y (SlotSet.second q.2).rev - y (SlotSet.first q.2).rev)) := by
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [slotPhase_coe, abs_mul, abs_of_pos (Real.exp_pos _),
    Real.mul_rpow (abs_nonneg _) (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  ring

theorem halfWeights_cancel (S : SlotSet (r + 1)) (m : ℕ → ℕ) (y : Fin (r + 1) → ℝ) :
    ∑ i, halfWeights S m i * y i.rev + ∑ q : S.starts, (m q : ℝ) / 2 *
      (y (SlotSet.second q.2).rev - y (SlotSet.first q.2).rev) = 0 := by
  have h := SlotSet.sum_mul_slotVec_real (S := S) (fun i => y i.rev)
    (fun q => (m q : ℝ) / 2) (fun q => -((m q : ℝ) / 2))
  rw [show ∑ i, halfWeights S m i * y i.rev = ∑ i, y i.rev * halfWeights S m i from
    Finset.sum_congr rfl fun i _ => mul_comm _ _]
  simp only [halfWeights] at h ⊢
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun q _ => ?_
  ring

theorem sum_rhoShift_rev (y : Fin (r + 1) → ℝ) :
    ∑ i, rhoShift i * y i.rev = -(torusModularLog (r + 1) y / 2) := by
  rw [torusModularLog_apply, ← Equiv.sum_comp Fin.revPerm (fun i => rhoShift i * y i.rev)]
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, rhoShift, Fin.val_rev]
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem blockWeight_le (S : SlotSet (r + 1)) (i : Fin (r + 1)) : blockWeight S i ≤ r := by
  have h1 : S.blockIdx i ≤ i := by
    unfold SlotSet.blockIdx
    exact (Finset.card_filter_le _ _).trans (by simp)
  have h2 : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  simp only [blockWeight]
  exact_mod_cast h1.trans h2

theorem neg_weight_rev_le (S : SlotSet (r + 1)) {δ : ℝ} (hδ : 0 ≤ δ) (y : Fin (r + 1) → ℝ) :
    -(δ * ∑ i, blockWeight S i * y i.rev) ≤ (r : ℝ) * δ * ∑ i, |y i| := by
  rw [← Equiv.sum_comp Fin.revPerm (fun i => |y i|), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Fin.revPerm_apply]
  have h0 : 0 ≤ blockWeight S i := by simp [blockWeight]
  have h1 := blockWeight_le S i
  have h2 : -y i.rev ≤ |y i.rev| := neg_le_abs _
  have h3 : 0 ≤ |y i.rev| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hδ h0),
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hδ h3)]

/-- **The bound on a vertical line.** On the line `Re t = δ > 0`, the deformed Jacquet family
satisfies the half-modulus bound with loss `exp(r δ Σ_i |y_i|)`, uniformly on the line. -/
theorem norm_canonical_deform_le (S : SlotSet (r + 1)) {p : Fin (r + 1) → Fin 2}
    {φ : U → ℂ} (hφ : IsCompactProfile p φ) (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0)
    {z : Fin (r + 1) → ℂ}
    (hz : ∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q)
    (hre : ∀ i, (z i).re = halfWeights S m i)
    (hmodes : SlotModes (slotsOf S m) (standardSection z φ)) (a : ℝˣ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℂ, t.re = δ → ∀ (y : Fin (r + 1) → ℝ) (k : K),
      ‖canonicalJacquetFamily a hφ (deform S z t) (torus y * k.val)‖ ≤
        A * Real.exp (torusModularLog (r + 1) y / 2 + (r : ℝ) * δ * ∑ i, |y i|) := by
  obtain ⟨C, hC, hb⟩ := norm_stagedIntegrand_le S hφ m hm hz hre hmodes
  set I := ∫ X : CoordC S.blockIdx → ℝ,
    spherical (sphExp S δ) (lowerCGL SlotSet.blockIdx_monotone X)
  have hI0 : 0 ≤ I := integral_nonneg fun X => (spherical_pos _ _).le
  set Pa := ∏ q : S.starts, |(a : ℝ)| ^ ((m q : ℝ) / 2)
  have hPa : 0 ≤ Pa := Finset.prod_nonneg fun q _ => Real.rpow_nonneg (abs_nonneg _) _
  have hh : (0 : ℝ) ≤ haarScale r a := (haarScale r a).2
  refine ⟨(haarScale r a : ℝ) * C * Pa * I, by positivity, fun t ht y k => ?_⟩
  rw [canonical_eq_stagedFamily S hφ m hm hz hre hmodes a y k.property (ht ▸ hδ)]
  set M := torusModularLog (r + 1) y
  set E2 := ∑ q : S.starts, (m q : ℝ) / 2 *
    (y (SlotSet.second q.2).rev - y (SlotSet.first q.2).rev)
  have hSI : ‖stagedIntegral S a y φ z k t‖ ≤ C * (Pa * Real.exp E2) * I := by
    calc ‖stagedIntegral S a y φ z k t‖
        ≤ ∫ X, C * (Pa * Real.exp E2) * spherical (sphExp S δ) (outerPt S X k) := by
          refine norm_integral_le_of_norm_le
            ((integrable_spherical_outerPt S hδ k.property).const_mul _)
            (Eventually.of_forall fun X => ?_)
          have := hb a y k t X
          rwa [prod_slotPhase, ht] at this
      _ = C * (Pa * Real.exp E2) * I := by
          rw [integral_const_mul, integral_spherical_outerPt S δ k.property]
  have hre1 : (∑ i, shiftExp (deform S z t) i * (y i.rev : ℂ)).re =
      ∑ i, halfWeights S m i * y i.rev - δ * ∑ i, blockWeight S i * y i.rev +
        ∑ i, rhoShift i * y i.rev := by
    rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (shiftExp (deform S z t) i).re = (deform S z t i).re + rhoShift i := by
      simp [shiftExp, rhoShift]
      ring
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, h1, deform_re,
      hre, ht]
    ring
  have hcan := halfWeights_cancel S m y
  have hrho := sum_rhoShift_rev (r := r) y
  have hw := neg_weight_rev_le S hδ.le y
  have hnorm : ‖stagedFamily S a y φ z k t‖ ≤
      (haarScale r a : ℝ) * C * Pa * I *
        Real.exp (M / 2 - δ * ∑ i, blockWeight S i * y i.rev) := by
    rw [stagedFamily, norm_mul, norm_mul, norm_mul, Complex.norm_exp, hre1, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_real, Real.norm_of_nonneg hh]
    calc Real.exp (∑ i, halfWeights S m i * y i.rev - δ * ∑ i, blockWeight S i * y i.rev +
            ∑ i, rhoShift i * y i.rev) * Real.exp M *
          ((haarScale r a : ℝ) * ‖stagedIntegral S a y φ z k t‖)
        ≤ Real.exp (∑ i, halfWeights S m i * y i.rev - δ * ∑ i, blockWeight S i * y i.rev +
            ∑ i, rhoShift i * y i.rev) * Real.exp M *
          ((haarScale r a : ℝ) * (C * (Pa * Real.exp E2) * I)) := by
          gcongr
      _ = (haarScale r a : ℝ) * C * Pa * I *
          Real.exp ((∑ i, halfWeights S m i * y i.rev + E2) - δ * ∑ i, blockWeight S i * y i.rev +
            ∑ i, rhoShift i * y i.rev + M) := by
          have hx : Real.exp ((∑ i, halfWeights S m i * y i.rev + E2) -
              δ * ∑ i, blockWeight S i * y i.rev + ∑ i, rhoShift i * y i.rev + M) =
              Real.exp (∑ i, halfWeights S m i * y i.rev - δ * ∑ i, blockWeight S i * y i.rev +
                ∑ i, rhoShift i * y i.rev) * Real.exp M * Real.exp E2 := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          rw [hx]
          ring
      _ = _ := by
          congr 2
          rw [hcan, hrho]
          ring
  refine hnorm.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  linarith

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
