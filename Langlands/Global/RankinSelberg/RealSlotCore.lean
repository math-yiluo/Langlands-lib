import Langlands.Global.RankinSelberg.RealSlotFourier
import Langlands.Global.RankinSelberg.RealDiscreteReciprocalFourier
import Langlands.Representation.Archimedean.RealInducedStandardBound

/-! # The joint rank-two open-cell integral over the slot coordinates -/

noncomputable section

open Complex MeasureTheory
open scoped FourierTransform
open Langlands.Archimedean
open Langlands.Archimedean.RealInducedBlockBound
open Langlands.Archimedean.RealInducedTorusCore
open Langlands.Archimedean.RealBlockFourierFinite
open Langlands.Global.RankinSelbergGlobal.RealDiscreteReciprocalFourier

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

variable {N : ℕ}

/-! ## Lists of slots of a slot set -/

theorem mkSlots_pairwise (S : SlotSet N) (m : ℕ → ℕ) : ∀ (L : List ℕ) (h : ∀ p ∈ L, p + 1 < N),
    (∀ p ∈ L, p ∈ S.starts) → L.Nodup → (mkSlots L h m).Pairwise Slot.Disjoint
  | [], _, _, _ => List.Pairwise.nil
  | p :: L, h, hS, hnd => by
    refine List.Pairwise.cons ?_ (mkSlots_pairwise S m L _ (fun q hq => hS q
      (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hnd).2)
    intro t ht
    obtain ⟨htL, _⟩ := mem_mkSlots ht
    have hpS := hS p List.mem_cons_self
    have htS := hS t.p (List.mem_cons_of_mem _ htL)
    have hne : t.p ≠ p := fun e => (List.nodup_cons.mp hnd).1 (e ▸ htL)
    have h1 : t.p ≠ p + 1 := fun e => S.sep p hpS (e ▸ htS)
    have h2 : p ≠ t.p + 1 := fun e => S.sep t.p htS (e ▸ hpS)
    change p + 1 < t.p ∨ t.p + 1 < p
    omega

/-- The mode attached to the position `q` by a list of positions and a list of modes. -/
def modeOf : List ℕ → List ℤ → ℕ → ℤ
  | p :: L, j :: J, q => if q = p then j else modeOf L J q
  | _, _, _ => 0

theorem modeProd_mkSlots (θ : ℕ → ℝ) (m : ℕ → ℕ) : ∀ (L : List ℕ) (h : ∀ p ∈ L, p + 1 < N)
    (J : List ℤ), L.Nodup → J.length = L.length →
      modeProd (mkSlots L h m) J θ = ∏ q ∈ L.toFinset, expMode (modeOf L J q) (θ q)
  | [], _, J, _, _ => by simp [mkSlots, modeProd]
  | p :: L, h, [], _, hJ => by simp at hJ
  | p :: L, h, j :: J, hnd, hJ => by
    have hpL : p ∉ L := (List.nodup_cons.mp hnd).1
    simp only [mkSlots, modeProd, List.toFinset_cons]
    rw [Finset.prod_insert (fun hh => hpL (List.mem_toFinset.mp hh)),
      modeProd_mkSlots θ m L _ J (List.nodup_cons.mp hnd).2 (by simpa using hJ)]
    simp only [modeOf]
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    have : q ≠ p := fun e => hpL (e ▸ List.mem_toFinset.mp hq)
    simp [this]

/-- Every slot of the list has an admissible mode. -/
def AllModes (slots : List (Slot N)) : Prop := ∀ t ∈ slots, IsMode t.M t.j

theorem allModes_withModes_mkSlots (m : ℕ → ℕ) : ∀ (L : List ℕ) (h : ∀ p ∈ L, p + 1 < N)
    (J : List ℤ), L.Nodup → J.length = L.length →
      (AllModes (withModes (mkSlots L h m) J) ↔ ∀ q ∈ L, IsMode (m q) (modeOf L J q))
  | [], _, J, _, _ => by simp [AllModes, mkSlots, withModes]
  | p :: L, h, [], _, hJ => by simp at hJ
  | p :: L, h, j :: J, hnd, hJ => by
    have hpL : p ∉ L := (List.nodup_cons.mp hnd).1
    have ih := allModes_withModes_mkSlots m L (fun q hq => h q (List.mem_cons_of_mem _ hq)) J
      (List.nodup_cons.mp hnd).2 (by simpa using hJ)
    simp only [AllModes, mkSlots, withModes, List.mem_cons, forall_eq_or_imp, setMode] at ih ⊢
    rw [ih]
    simp only [modeOf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun q hq => ?_⟩
      have : q ≠ p := fun e => hpL (e ▸ hq)
      simpa [this] using h2 q hq
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun q hq => ?_⟩
      have : q ≠ p := fun e => hpL (e ▸ hq)
      simpa [this] using h2 q hq

/-! ## Vanishing of the inadmissible coefficients -/

/-- The inadmissible Fourier coefficients along the slots of the list vanish on `O(N)`. -/
def SlotModes (slots : List (Slot N)) (u : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  ∀ t ∈ slots, ∀ j : ℤ, ¬ IsMode t.M j → ∀ k ∈ unitaryCompact ℝ N,
    blockFourierCoefficient N t.p j u k = 0

theorem slotModes_blockFourierCoefficient {s : Slot N} {slots : List (Slot N)}
    (hsd : ∀ t ∈ slots, s.p + 1 < t.p ∨ t.p + 1 < s.p) {u : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : Continuous u) (hm : SlotModes slots u) (j : ℤ) :
    SlotModes slots (blockFourierCoefficient N s.p j u) := by
  intro t ht j' hj' k hk
  have hcomm := blockFourierCoefficient_comm (N := N) (p := t.p) (p' := s.p)
    (by rcases hsd t ht with h | h <;> [exact Or.inr h; exact Or.inl h]) hu j' j k
  rw [hcomm]
  exact blockFourierCoefficient_eq_zero_of j fun θ =>
    hm t ht j' hj' _ (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)

theorem slotModes_coeffs {slots : List (Slot N)} {u : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : Continuous u) (hm : SlotModes slots u) : ∀ (L : List (Slot N)),
      (∀ s ∈ L, ∀ t ∈ slots, s.p + 1 < t.p ∨ t.p + 1 < s.p) → SlotModes slots (coeffs L u)
  | [], _ => hm
  | s :: L, hd => slotModes_blockFourierCoefficient (hd s List.mem_cons_self)
      (continuous_coeffs hu L) (slotModes_coeffs hu hm L fun s' hs' => hd s'
        (List.mem_cons_of_mem _ hs')) s.j

theorem coeffs_withModes_eq_zero {u : Langlands.GeneralLinear N ℝ → ℂ} (hu : Continuous u) :
    ∀ (slots : List (Slot N)) (J : List ℤ), slots.Pairwise Slot.Disjoint →
      SlotModes slots u → ¬ AllModes (withModes slots J) →
        ∀ k ∈ unitaryCompact ℝ N, coeffs (withModes slots J) u k = 0
  | [], J, _, _, hbad, k, _ => by
    exact absurd (by intro t ht; cases J <;> simp [withModes] at ht) hbad
  | s :: rest, [], _, _, hbad, k, _ => by
    exact absurd (by intro t ht; simp [withModes] at ht) hbad
  | s :: rest, j :: J, hpw, hm, hbad, k, hk => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hm' : SlotModes rest u := fun t ht => hm t (List.mem_cons_of_mem _ ht)
    change blockFourierCoefficient N s.p j (coeffs (withModes rest J) u) k = 0
    by_cases hj : IsMode s.M j
    · have hbad' : ¬ AllModes (withModes rest J) := by
        intro hall
        apply hbad
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact hj
        · exact hall t ht
      exact blockFourierCoefficient_eq_zero_of j fun θ =>
        coeffs_withModes_eq_zero hu rest J hrest hm' hbad' _
          (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)
    · have hd : ∀ s' ∈ withModes rest J, ∀ t ∈ [s], s'.p + 1 < t.p ∨ t.p + 1 < s'.p := by
        intro s' hs' t ht
        obtain ⟨t', ht', j', rfl⟩ := mem_withModes hs'
        rw [List.mem_singleton] at ht
        subst ht
        rcases hsd t' ht' with h | h <;> [exact Or.inr h; exact Or.inl h]
      have := slotModes_coeffs hu (slots := [s]) (fun t ht => hm t (by
        rw [List.mem_singleton] at ht; subst ht; exact List.mem_cons_self))
        (withModes rest J) hd
      exact this s List.mem_cons_self j hj k hk

/-- The slot conditions only involve the values on `O(N)`. -/
theorem hasDegree_congr {slots : List (Slot N)} {D : ℕ} {u v : Langlands.GeneralLinear N ℝ → ℂ}
    (huv : ∀ k ∈ unitaryCompact ℝ N, u k = v k) (hu : HasDegree slots D u) :
    HasDegree slots D v := by
  intro t ht j hj k hk
  rw [← hu t ht j hj k hk]
  exact (coeffs_congr_of_eqOn huv [setMode t j] k hk).symm

theorem slotModes_congr {slots : List (Slot N)} {u v : Langlands.GeneralLinear N ℝ → ℂ}
    (huv : ∀ k ∈ unitaryCompact ℝ N, u k = v k) (hu : SlotModes slots u) :
    SlotModes slots v := by
  intro t ht j hj k hk
  rw [← hu t ht j hj k hk]
  exact (coeffs_congr_of_eqOn huv [setMode t j] k hk).symm

/-! ## The angular kernels -/

theorem norm_angularKernel (k : ℕ) (j : ℤ) (x : ℝ) :
    ‖angularKernel k j x‖ = (cellNorm x)⁻¹ ^ (k + 1) := by
  have hρ := cellNorm_pos x
  have he : ‖expMode j (Real.arctan x)‖ = 1 := by
    rw [expMode, show ((j : ℂ) * ((Real.arctan x : ℝ) : ℂ) * Complex.I) =
      ((j * Real.arctan x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  simp only [angularKernel, norm_mul, norm_pow, norm_inv, Complex.norm_real, he, mul_one]
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rfl

theorem continuous_angularKernel (k : ℕ) (j : ℤ) : Continuous (angularKernel k j) := by
  unfold angularKernel
  refine Continuous.mul ?_ ((continuous_expMode j).comp Real.continuous_arctan)
  refine Continuous.pow (Continuous.inv₀ ?_ fun x => ?_) _
  · exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop))
  · exact Complex.ofReal_ne_zero.mpr (cellNorm_pos x).ne'

theorem integrable_angularKernel {k : ℕ} (hk : k ≠ 0) (j : ℤ) : Integrable (angularKernel k j) := by
  refine (integrable_inv_one_add_sq).mono' (continuous_angularKernel k j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_angularKernel]
  have h1 : 1 ≤ cellNorm x := by
    rw [cellNorm]
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg x])
  have hsq := cellNorm_sq x
  have hpos := cellNorm_pos x
  calc (cellNorm x)⁻¹ ^ (k + 1) ≤ (cellNorm x)⁻¹ ^ 2 :=
        pow_le_pow_of_le_one (inv_nonneg.mpr hpos.le) (inv_le_one_of_one_le₀ h1) (by omega)
    _ = (1 + x ^ 2)⁻¹ := by rw [inv_pow, hsq]

theorem angularKernel_fourier_half {k : ℕ} (hk : k ≠ 0) {j : ℤ} (hj : IsMode k j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖𝓕 (angularKernel k j) y‖ ≤ C * |y| ^ ((k : ℝ) / 2) := by
  obtain ⟨l, hl⟩ := hj
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  exact (angularKernel_fourier_bound k l hk hl (by positivity) (by linarith)).2

open Classical in
/-- A constant for the Fourier bound of an admissible angular kernel, and zero otherwise. -/
def angConst (k : ℕ) (j : ℤ) : ℝ :=
  if h : k ≠ 0 ∧ IsMode k j then Classical.choose (angularKernel_fourier_half h.1 h.2) else 0

theorem angConst_nonneg (k : ℕ) (j : ℤ) : 0 ≤ angConst k j := by
  unfold angConst
  split_ifs with h
  · exact (Classical.choose_spec (angularKernel_fourier_half h.1 h.2)).1
  · exact le_rfl

theorem norm_fourier_angularKernel_le {k : ℕ} (hk : k ≠ 0) {j : ℤ} (hj : IsMode k j) (y : ℝ) :
    ‖𝓕 (angularKernel k j) y‖ ≤ angConst k j * |y| ^ ((k : ℝ) / 2) := by
  have h : k ≠ 0 ∧ IsMode k j := ⟨hk, hj⟩
  unfold angConst
  rw [dite_eq_left h]
  exact (Classical.choose_spec (angularKernel_fourier_half h.1 h.2)).2 y

theorem integral_angularKernel_phase (k : ℕ) (j : ℤ) (c : ℝ) :
    ∫ t : ℝ, angularKernel k j t * Complex.exp (((2 * Real.pi * c * t : ℝ) : ℂ) * Complex.I) =
      𝓕 (angularKernel k j) (-c) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 3
  push_cast
  ring


/-! ## The core integral over the slot coordinates -/

/-- The angles `arctan x_q` at the slot starts, and zero elsewhere. -/
def arcVec (S : SlotSet N) (x : S.starts → ℝ) (p : ℕ) : ℝ :=
  if h : p ∈ S.starts then Real.arctan (x ⟨p, h⟩) else 0

/-- The sorted list of slot starts. -/
def startList (S : SlotSet N) : List ℕ := S.starts.sort (· ≤ ·)

theorem startList_lt (S : SlotSet N) : ∀ p ∈ startList S, p + 1 < N :=
  fun p hp => S.lt p (by simpa [startList] using hp)

/-- The slots of a slot set, in increasing order, with weights `m`. -/
def slotsOf (S : SlotSet N) (m : ℕ → ℕ) : List (Slot N) := mkSlots (startList S) (startList_lt S) m

theorem startList_toFinset (S : SlotSet N) : (startList S).toFinset = S.starts := by
  simp [startList]

theorem startList_nodup (S : SlotSet N) : (startList S).Nodup := Finset.sort_nodup _ _

theorem slotsOf_pairwise (S : SlotSet N) (m : ℕ → ℕ) : (slotsOf S m).Pairwise Slot.Disjoint :=
  mkSlots_pairwise S m _ _ (fun p hp => by simpa [startList] using hp) (startList_nodup S)

theorem length_slotsOf (S : SlotSet N) (m : ℕ → ℕ) :
    (slotsOf S m).length = S.starts.card := by
  rw [slotsOf, length_mkSlots, startList, Finset.length_sort]

/-- The Fourier expansion of the slot kernel `∏ ρ(y_q)^{-(m_q+1)} u(r(arctan y) k)`. -/
theorem slotKernel_eq (S : SlotSet N) (m : ℕ → ℕ) {u : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : Continuous u) (hK : IsKFin u) {D : ℕ} (hdeg : HasDegree (slotsOf S m) D u)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) (y : S.starts → ℝ) :
    (∏ q : S.starts, ((cellNorm (y q) : ℝ) : ℂ)⁻¹ ^ (m q + 1)) * u (S.rot (arcVec S y) * k) =
      (2 * (Real.pi : ℂ))⁻¹ ^ (slotsOf S m).length * ∑ J ∈ modeLists D (slotsOf S m).length,
        coeffs (withModes (slotsOf S m) J) u k *
          ∏ q : S.starts, angularKernel (m q) (modeOf (startList S) J q) (y q) := by
  rw [rot_eq_rotProd (arcVec S y) m (startList S) S (startList_toFinset S).symm
    (startList_nodup S) (startList_lt S)]
  rw [show mkSlots (startList S) (startList_lt S) m = slotsOf S m from rfl]
  rw [eq_sum_rotProd D (slotsOf S m) (slotsOf_pairwise S m) hu hK hdeg k hk]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hlen : J.length = (startList S).length := by
    rw [(mem_modeLists hJ).1, slotsOf, length_mkSlots]
  have hmode : modeProd (slotsOf S m) J (arcVec S y) =
      ∏ q : S.starts, expMode (modeOf (startList S) J q) (Real.arctan (y q)) := by
    rw [slotsOf, modeProd_mkSlots _ m _ _ J (startList_nodup S) hlen, startList_toFinset,
      ← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun q _ => ?_
    simp [arcVec, q.2]
  rw [hmode]
  simp only [angularKernel, Finset.prod_mul_distrib, cellNorm]
  ring

/-- The affine slot coordinates `(x_q + c_q) s_q`. -/
def affineCoord (S : SlotSet N) (c s : ℕ → ℝ) (x : S.starts → ℝ) : S.starts → ℝ :=
  fun q => (x q + c q) * s q

/-- The core integrand on the product of the slot coordinates: the product over the slots of
`ρ(y_q)^{-(m_q+1)}`, the function `u` at the joint rotation `rot S (arctan y) · k`, and the slotwise
phase `exp(2πi Σ_q b_q x_q)`, in the affine coordinates `y_q = (x_q + c_q) s_q`. -/
def coreIntegrand (S : SlotSet N) (m : ℕ → ℕ) (u : Langlands.GeneralLinear N ℝ → ℂ)
    (k : Langlands.GeneralLinear N ℝ) (b c s : ℕ → ℝ) (x : S.starts → ℝ) : ℂ :=
  (∏ q : S.starts, ((cellNorm (affineCoord S c s x q) : ℝ) : ℂ)⁻¹ ^ (m q + 1)) *
    u (S.rot (arcVec S (affineCoord S c s x)) * k) *
    Complex.exp (((2 * Real.pi * ∑ q : S.starts, b q * x q : ℝ) : ℂ) * Complex.I)

/-- One term of the expansion of the core integrand. -/
def coreTerm (S : SlotSet N) (m : ℕ → ℕ) (b c s : ℕ → ℝ) (J : List ℤ)
    (x : S.starts → ℝ) : ℂ :=
  ∏ q : S.starts, (angularKernel (m q) (modeOf (startList S) J q) ((x q + c q) * s q) *
    Complex.exp (((2 * Real.pi * b q * x q : ℝ) : ℂ) * Complex.I))

theorem coreIntegrand_eq (S : SlotSet N) (m : ℕ → ℕ) {u : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : Continuous u) (hK : IsKFin u) {D : ℕ} (hdeg : HasDegree (slotsOf S m) D u)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) (b c s : ℕ → ℝ)
    (x : S.starts → ℝ) :
    coreIntegrand S m u k b c s x =
      (2 * (Real.pi : ℂ))⁻¹ ^ (slotsOf S m).length * ∑ J ∈ modeLists D (slotsOf S m).length,
        coeffs (withModes (slotsOf S m) J) u k * coreTerm S m b c s J x := by
  unfold coreIntegrand
  rw [slotKernel_eq S m hu hK hdeg hk]
  have hphase : Complex.exp (((2 * Real.pi * ∑ q : S.starts, b q * x q : ℝ) : ℂ) * Complex.I) =
      ∏ q : S.starts, Complex.exp (((2 * Real.pi * b q * x q : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hphase, mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [coreTerm, affineCoord, Finset.prod_mul_distrib]
  ring

theorem integrable_angularKernel_affine {k : ℕ} (hk : k ≠ 0) (j : ℤ) (b c : ℝ) {s : ℝ}
    (hs : 0 < s) :
    Integrable fun t : ℝ => angularKernel k j ((t + c) * s) *
      Complex.exp (((2 * Real.pi * b * t : ℝ) : ℂ) * Complex.I) := by
  have h1 : Integrable fun t : ℝ => angularKernel k j ((t + c) * s) :=
    ((integrable_angularKernel hk j).comp_mul_right' hs.ne').comp_add_right c
  refine h1.norm.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact (((continuous_angularKernel k j).comp ((continuous_id.add continuous_const).mul
      continuous_const)).mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem integral_angularKernel_affine (k : ℕ) (j : ℤ) (b c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ, angularKernel k j ((t + c) * s) *
        Complex.exp (((2 * Real.pi * b * t : ℝ) : ℂ) * Complex.I) =
      (s⁻¹ : ℂ) * Complex.exp (((-(2 * Real.pi * b * c)) : ℝ) * Complex.I) *
        𝓕 (angularKernel k j) (-(b / s)) := by
  let h : ℝ → ℂ := fun y => angularKernel k j y *
    Complex.exp (((2 * Real.pi * b * (y / s - c)) : ℝ) * Complex.I)
  have he : (fun t : ℝ => angularKernel k j ((t + c) * s) *
      Complex.exp (((2 * Real.pi * b * t : ℝ) : ℂ) * Complex.I)) =
      fun t => (fun t' => h (t' * s)) (t + c) := by
    funext t
    have ht : (t + c) * s / s - c = t := by rw [mul_div_assoc, div_self hs.ne', mul_one]; ring
    simp only [h, ht]
  rw [he, MeasureTheory.integral_add_right_eq_self (fun t' => h (t' * s)),
    MeasureTheory.Measure.integral_comp_mul_right h s]
  have hint : ∫ y, h y = Complex.exp (((-(2 * Real.pi * b * c)) : ℝ) * Complex.I) *
      𝓕 (angularKernel k j) (-(b / s)) := by
    rw [← integral_angularKernel_phase, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [h]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [hint, abs_inv, abs_of_pos hs, Complex.real_smul]
  push_cast
  ring

theorem integrable_coreTerm (S : SlotSet N) {m : ℕ → ℕ} (hm : ∀ p ∈ S.starts, m p ≠ 0)
    (b c s : ℕ → ℝ) (hs : ∀ p ∈ S.starts, 0 < s p) (J : List ℤ) :
    Integrable (coreTerm S m b c s J) :=
  Integrable.fintype_prod (f := fun (q : S.starts) (t : ℝ) =>
      angularKernel (m q) (modeOf (startList S) J q) ((t + c q) * s q) *
        Complex.exp (((2 * Real.pi * b q * t : ℝ) : ℂ) * Complex.I))
    fun q => integrable_angularKernel_affine (hm q q.2) _ _ _ (hs q q.2)

theorem integral_coreTerm (S : SlotSet N) (m : ℕ → ℕ) (b c s : ℕ → ℝ)
    (hs : ∀ p ∈ S.starts, 0 < s p) (J : List ℤ) :
    ∫ x, coreTerm S m b c s J x =
      ∏ q : S.starts, ((s q)⁻¹ : ℂ) * Complex.exp (((-(2 * Real.pi * b q * c q)) : ℝ) * Complex.I) *
        𝓕 (angularKernel (m q) (modeOf (startList S) J q)) (-(b q / s q)) := by
  unfold coreTerm
  rw [integral_fintype_prod_volume_eq_prod (f := fun (q : S.starts) (t : ℝ) =>
      angularKernel (m q) (modeOf (startList S) J q) ((t + c q) * s q) *
        Complex.exp (((2 * Real.pi * b q * t : ℝ) : ℂ) * Complex.I))]
  exact Finset.prod_congr rfl fun q _ => integral_angularKernel_affine _ _ _ _ (hs q q.2)

/-- The constant of the core bound for a degree bound `D` and a bound `B` on `O(N)`. -/
def coreConstant (S : SlotSet N) (m : ℕ → ℕ) (D : ℕ) (B : ℝ) : ℝ :=
  max B 0 * ∑ J ∈ modeLists D (slotsOf S m).length,
    ∏ q : S.starts, angConst (m q) (modeOf (startList S) J q)

theorem coreConstant_nonneg (S : SlotSet N) (m : ℕ → ℕ) (D : ℕ) (B : ℝ) :
    0 ≤ coreConstant S m D B :=
  mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun _ _ =>
    Finset.prod_nonneg fun _ _ => angConst_nonneg _ _)

/-- **The core bound.** Let the weights `m_q` be nonzero on the slots. For a continuous right
`O(N)`-finite function of degree at most `D` along the slots, whose inadmissible Fourier
coefficients along the slots vanish and which is bounded by `B` on `O(N)`, the integral
of the core integrand over the product of the slot coordinates, in the affine coordinates
`(x_q + c_q) s_q` with the slotwise phase `exp(2πi Σ_q b_q x_q)`, is bounded by
`C ∏_q s_q⁻¹ |b_q / s_q|^{m_q/2}`, uniformly in `k ∈ O(N)`, `b`, `c` and `s > 0`. The integral
factors into one-variable integrals term by term in the Fourier expansion along the slots. -/
theorem core_bound (S : SlotSet N) (m : ℕ → ℕ) (hm : ∀ p ∈ S.starts, m p ≠ 0)
    {u : Langlands.GeneralLinear N ℝ → ℂ} (hu : Continuous u) (hK : IsKFin u) {D : ℕ}
    (hdeg : HasDegree (slotsOf S m) D u)
    (hmodes : SlotModes (slotsOf S m) u) {B : ℝ} (hB : ∀ k ∈ unitaryCompact ℝ N, ‖u k‖ ≤ B)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) (b c s : ℕ → ℝ)
    (hs : ∀ p ∈ S.starts, 0 < s p) :
      Integrable (coreIntegrand S m u k b c s) ∧
        ‖∫ x, coreIntegrand S m u k b c s x‖ ≤
          coreConstant S m D B * ∏ q : S.starts, ((s q)⁻¹ * |b q / s q| ^ ((m q : ℝ) / 2)) := by
  set r := (slotsOf S m).length with hr
  set L := startList S
  let B' := max B 0
  have hB' : ∀ k ∈ unitaryCompact ℝ N, ‖u k‖ ≤ B' := fun k hk => (hB k hk).trans (le_max_left _ _)
  have hB'0 : 0 ≤ B' := le_max_right _ _
  let C := coreConstant S m D B
  have hfun : coreIntegrand S m u k b c s = fun x => (2 * (Real.pi : ℂ))⁻¹ ^ r *
      ∑ J ∈ modeLists D r, coeffs (withModes (slotsOf S m) J) u k * coreTerm S m b c s J x := by
    funext x
    exact coreIntegrand_eq S m hu hK hdeg hk b c s x
  have hint : Integrable fun x => (2 * (Real.pi : ℂ))⁻¹ ^ r *
      ∑ J ∈ modeLists D r, coeffs (withModes (slotsOf S m) J) u k * coreTerm S m b c s J x :=
    (integrable_finsetSum _ fun J _ => (integrable_coreTerm S hm b c s hs J).const_mul _).const_mul _
  refine ⟨hfun ▸ hint, ?_⟩
  rw [hfun, integral_const_mul, integral_finsetSum _ fun J _ =>
    (integrable_coreTerm S hm b c s hs J).const_mul _]
  simp_rw [integral_const_mul, integral_coreTerm S m b c s hs]
  set P := ∏ q : S.starts, ((s q)⁻¹ * |b q / s q| ^ ((m q : ℝ) / 2))
  have hP : 0 ≤ P := Finset.prod_nonneg fun q _ =>
    mul_nonneg (inv_nonneg.mpr (hs q q.2).le) (Real.rpow_nonneg (abs_nonneg _) _)
  have hterm : ∀ J ∈ modeLists D r,
      ‖coeffs (withModes (slotsOf S m) J) u k *
        ∏ q : S.starts, ((s q)⁻¹ : ℂ) * Complex.exp (((-(2 * Real.pi * b q * c q)) : ℝ) * Complex.I) *
          𝓕 (angularKernel (m q) (modeOf L J q)) (-(b q / s q))‖ ≤
      (2 * Real.pi) ^ r * B' * ((∏ q : S.starts, angConst (m q) (modeOf L J q)) * P) := by
    intro J hJ
    have hJlen : J.length = (slotsOf S m).length := (mem_modeLists hJ).1
    have hJlen' : J.length = L.length := by
      rw [hJlen, slotsOf, length_mkSlots]
    by_cases hall : AllModes (withModes (slotsOf S m) J)
    · have hq : ∀ q ∈ L, IsMode (m q) (modeOf L J q) :=
        (allModes_withModes_mkSlots m L (startList_lt S) J (startList_nodup S) hJlen').mp hall
      rw [norm_mul, norm_prod]
      have hcoef := norm_coeffs_le_of_mem hB' (withModes (slotsOf S m) J) k hk
      rw [length_withModes _ _ hJlen] at hcoef
      have hprod : ∏ q : S.starts, ‖((s q)⁻¹ : ℂ) *
            Complex.exp (((-(2 * Real.pi * b q * c q)) : ℝ) * Complex.I) *
            𝓕 (angularKernel (m q) (modeOf L J q)) (-(b q / s q))‖ ≤
          (∏ q : S.starts, angConst (m q) (modeOf L J q)) * P := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀ (fun q _ => norm_nonneg _) fun q _ => ?_
        have hqL : (q : ℕ) ∈ L := by
          rw [← List.mem_toFinset, startList_toFinset]; exact q.2
        have h := norm_fourier_angularKernel_le (hm q q.2) (hq q hqL) (-(b q / s q))
        rw [abs_neg] at h
        have hsq := hs q q.2
        rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg hsq.le]
        calc (s q)⁻¹ * ‖𝓕 (angularKernel (m q) (modeOf L J q)) (-(b q / s q))‖
            ≤ (s q)⁻¹ * (angConst (m q) (modeOf L J q) * |b q / s q| ^ ((m q : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hsq.le)
          _ = _ := by ring
      calc ‖coeffs (withModes (slotsOf S m) J) u k‖ * ∏ q : S.starts, ‖((s q)⁻¹ : ℂ) *
            Complex.exp (((-(2 * Real.pi * b q * c q)) : ℝ) * Complex.I) *
            𝓕 (angularKernel (m q) (modeOf L J q)) (-(b q / s q))‖
          ≤ ((2 * Real.pi) ^ r * B') * ((∏ q : S.starts, angConst (m q) (modeOf L J q)) * P) :=
            mul_le_mul hcoef hprod (Finset.prod_nonneg fun q _ => norm_nonneg _)
              (mul_nonneg (pow_nonneg (by positivity) _) hB'0)
        _ = _ := by ring
    · rw [coeffs_withModes_eq_zero hu _ J (slotsOf_pairwise S m) hmodes hall k hk, zero_mul,
        norm_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) hB'0)
        (mul_nonneg (Finset.prod_nonneg fun q _ => angConst_nonneg _ _) hP)
  calc ‖(2 * (Real.pi : ℂ))⁻¹ ^ r * ∑ J ∈ modeLists D r, coeffs (withModes (slotsOf S m) J) u k *
        ∏ q : S.starts, ((s q)⁻¹ : ℂ) * Complex.exp (((-(2 * Real.pi * b q * c q)) : ℝ) * Complex.I) *
          𝓕 (angularKernel (m q) (modeOf L J q)) (-(b q / s q))‖
      ≤ (2 * Real.pi)⁻¹ ^ r * ∑ J ∈ modeLists D r,
          (2 * Real.pi) ^ r * B' * ((∏ q : S.starts, angConst (m q) (modeOf L J q)) * P) := by
        rw [norm_mul, norm_pow, norm_inv]
        have h2 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
          rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        rw [h2]
        exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
          (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
    _ = C * P := by
        rw [← Finset.mul_sum, ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity),
          one_pow, one_mul]
        simp only [C, coreConstant, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        ring

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
