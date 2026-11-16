import Langlands.Representation.Archimedean.RealInducedBlockInvariance

/-!
# Torus pairings along induced blocks

For pairwise disjoint blocks `p_1, …, p_r` of `GL_N(ℝ)` the iterated rotation average
`coeffs (zeroModes slots) F 1 = ∫ F(r_{p_1}(θ_1) ⋯ r_{p_r}(θ_r)) dθ` integrates `F` over the
torus of rotations of these blocks. This module computes such averages for products
`x ↦ u(x k) h(x g)` with `k ∈ O(N)` and `u` right `O(N)`-finite (Parseval,
`coeffs_zeroModes_mul_eq_sum`), and the averages of block covariant functions with tied exponents
at `point slots` (`coeffs_zeroModes_point`). Together with the multi-block bound this gives the
core torus bound `norm_coeffs_zeroModes_le`: the torus average of `u(· k) h(· b k')` is bounded by
a constant times the torus average of a tied exponential function.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

namespace RealInducedTorusCore

open RealBlockRotation RealBlockFourierFinite RealInducedBlockSlice RealInducedBlockBound
  RealBlockJacquet

variable {N : ℕ}

/-! ## Modes -/

/-- The slot `s` with the Fourier mode `j`. -/
def setMode (s : Slot N) (j : ℤ) : Slot N :=
  { s with j := j }

/-- The slots with the modes of the list `J`. -/
def withModes : List (Slot N) → List ℤ → List (Slot N)
  | s :: rest, j :: J => setMode s j :: withModes rest J
  | _, _ => []

/-- All slots with the mode `0`. -/
def zeroModes (slots : List (Slot N)) : List (Slot N) :=
  slots.map fun s => setMode s 0

/-- The lists of `r` modes in `[-D, D]`. -/
def modeLists (D : ℕ) : ℕ → Finset (List ℤ)
  | 0 => {[]}
  | r + 1 => ((Finset.Icc (-(D : ℤ)) D) ×ˢ modeLists D r).image fun x => x.1 :: x.2

theorem sum_modeLists_succ {β : Type*} [AddCommMonoid β] (D r : ℕ) (f : List ℤ → β) :
    ∑ J ∈ modeLists D (r + 1), f J =
      ∑ j ∈ Finset.Icc (-(D : ℤ)) D, ∑ J ∈ modeLists D r, f (j :: J) := by
  rw [modeLists, Finset.sum_image, Finset.sum_product]
  rintro ⟨a, A⟩ _ ⟨b, B⟩ _ h
  simp only [List.cons.injEq] at h
  rw [h.1, h.2]

theorem card_modeLists (D : ℕ) : ∀ r : ℕ, (modeLists D r).card = (2 * D + 1) ^ r
  | 0 => rfl
  | r + 1 => by
    rw [modeLists, Finset.card_image_of_injective, Finset.card_product, card_modeLists D r,
      Int.card_Icc, pow_succ]
    · have : ((D : ℤ) + 1 - -(D : ℤ)).toNat = 2 * D + 1 := by omega
      rw [this, mul_comm]
    · rintro ⟨a, A⟩ ⟨b, B⟩ h
      simp only [List.cons.injEq] at h
      rw [h.1, h.2]

theorem mem_modeLists {D : ℕ} : ∀ {r : ℕ} {J : List ℤ}, J ∈ modeLists D r →
    J.length = r ∧ ∀ j ∈ J, |j| ≤ D
  | 0, J, hJ => by
    rw [modeLists, Finset.mem_singleton] at hJ
    subst hJ
    simp
  | r + 1, J, hJ => by
    rw [modeLists, Finset.mem_image] at hJ
    obtain ⟨⟨j, J'⟩, hm, rfl⟩ := hJ
    rw [Finset.mem_product, Finset.mem_Icc] at hm
    obtain ⟨hl, hb⟩ := mem_modeLists hm.2
    refine ⟨by simp [hl], ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact abs_le.mpr hm.1
    · exact hb i hi

theorem mem_withModes : ∀ {slots : List (Slot N)} {J : List ℤ} {t : Slot N},
    t ∈ withModes slots J → ∃ s ∈ slots, ∃ j : ℤ, t = setMode s j
  | [], _, _, ht => by simp [withModes] at ht
  | _ :: _, [], _, ht => by simp [withModes] at ht
  | s :: rest, j :: J, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨s, List.mem_cons_self, j, rfl⟩
    · obtain ⟨s', hs', j', rfl⟩ := mem_withModes ht
      exact ⟨s', List.mem_cons_of_mem _ hs', j', rfl⟩

theorem pairwise_withModes : ∀ {slots : List (Slot N)} (J : List ℤ),
    slots.Pairwise Slot.Disjoint → (withModes slots J).Pairwise Slot.Disjoint
  | [], _, _ => by simp [withModes]
  | _ :: _, [], _ => by simp [withModes]
  | s :: rest, j :: J, hpw => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    refine List.pairwise_cons.mpr ⟨fun t ht => ?_, pairwise_withModes J hrest⟩
    obtain ⟨s', hs', j', rfl⟩ := mem_withModes ht
    exact hsd s' hs'

theorem pairwise_zeroModes {slots : List (Slot N)} (hpw : slots.Pairwise Slot.Disjoint) :
    (zeroModes slots).Pairwise Slot.Disjoint :=
  List.pairwise_map.mpr (hpw.imp fun h => h)

theorem point_withModes : ∀ (slots : List (Slot N)) (J : List ℤ), J.length = slots.length →
    point (withModes slots J) = point slots
  | [], _, _ => by simp [withModes]
  | _ :: _, [], h => by simp at h
  | s :: rest, j :: J, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp only [withModes, point]
    rw [point_withModes rest J h]
    rfl

theorem expBound_withModes : ∀ (slots : List (Slot N)) (J : List ℤ), J.length = slots.length →
    expBound (withModes slots J) = expBound slots
  | [], _, _ => by simp [withModes]
  | _ :: _, [], h => by simp at h
  | s :: rest, j :: J, h => by
    simp only [List.length_cons, add_left_inj] at h
    have := expBound_withModes rest J h
    simp only [expBound, withModes, List.map_cons, List.prod_cons] at this ⊢
    rw [this]
    rfl

theorem length_withModes : ∀ (slots : List (Slot N)) (J : List ℤ), J.length = slots.length →
    (withModes slots J).length = slots.length
  | [], _, _ => by simp [withModes]
  | _ :: _, [], h => by simp at h
  | s :: rest, j :: J, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp [withModes, length_withModes rest J h]

theorem inClass_withModes {slots : List (Slot N)} {D : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : InClass slots D F) (J : List ℤ) : InClass (withModes slots J) D F := by
  refine ⟨hF.1, hF.2.1, fun t ht => ?_⟩
  obtain ⟨s, hs, j, rfl⟩ := mem_withModes ht
  exact hF.2.2 s hs

/-- The constant of the multi-block bound for modes in `[-D, D]`. -/
theorem const_withModes_le (D : ℕ) : ∀ (slots : List (Slot N)) (J : List ℤ),
    J.length = slots.length → (∀ j ∈ J, |j| ≤ D) →
    const (withModes slots J) D ≤ ((2 : ℝ) ^ (3 * D) * (2 * D + 1) * (2 * Real.pi)) ^ slots.length
  | [], _, _, _ => by simp [withModes, const]
  | _ :: _, [], h, _ => by simp at h
  | s :: rest, j :: J, h, hJ => by
    simp only [List.length_cons, add_left_inj] at h
    have IH := const_withModes_le D rest J h fun i hi => hJ i (List.mem_cons_of_mem _ hi)
    have hj : j.natAbs ≤ D := by
      have := hJ j List.mem_cons_self
      rw [Int.abs_eq_natAbs] at this
      omega
    have h1 : (2 : ℝ) ^ (j.natAbs + 2 * D) ≤ 2 ^ (3 * D) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h0 : 0 ≤ const (withModes rest J) D := by
      unfold const
      exact List.prod_nonneg fun x hx => by
        obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
        positivity
    simp only [withModes, const, List.map_cons, List.prod_cons, List.length_cons] at IH h0 ⊢
    rw [pow_succ']
    have hc : 0 ≤ (2 * (D : ℝ) + 1) * (2 * Real.pi) := by positivity
    calc (2 : ℝ) ^ ((setMode s j).j.natAbs + 2 * D) * (2 * D + 1) * (2 * Real.pi) *
          (List.map (fun s => (2 : ℝ) ^ (s.j.natAbs + 2 * D) * (2 * D + 1) * (2 * Real.pi))
            (withModes rest J)).prod ≤
        (2 : ℝ) ^ (3 * D) * (2 * D + 1) * (2 * Real.pi) *
          ((2 : ℝ) ^ (3 * D) * (2 * D + 1) * (2 * Real.pi)) ^ rest.length := by
          have e : (2 : ℝ) ^ ((setMode s j).j.natAbs + 2 * D) * (2 * D + 1) * (2 * Real.pi) =
              (2 : ℝ) ^ (j.natAbs + 2 * D) * ((2 * D + 1) * (2 * Real.pi)) := by
            simp only [setMode]
            ring
          rw [e, show (2 : ℝ) ^ (3 * D) * (2 * D + 1) * (2 * Real.pi) =
            (2 : ℝ) ^ (3 * D) * ((2 * D + 1) * (2 * Real.pi)) by ring]
          gcongr
          exact IH.trans_eq (by ring)

/-! ## Basic properties of iterated coefficients -/

theorem coeffs_mul_right (F : Langlands.GeneralLinear N ℝ → ℂ) (g : Langlands.GeneralLinear N ℝ) :
    ∀ (L : List (Slot N)) (x : Langlands.GeneralLinear N ℝ),
      coeffs L F (x * g) = coeffs L (fun y => F (y * g)) x
  | [], _ => rfl
  | s :: L, x => by
    simp only [coeffs]
    unfold blockFourierCoefficient
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [← mul_assoc, coeffs_mul_right F g L]

theorem coeffs_congr_of_eqOn {F F' : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : ∀ k ∈ unitaryCompact ℝ N, F k = F' k) :
    ∀ (L : List (Slot N)) (k : Langlands.GeneralLinear N ℝ), k ∈ unitaryCompact ℝ N →
      coeffs L F k = coeffs L F' k
  | [], k, hk => hF k hk
  | s :: L, k, hk => by
    simp only [coeffs]
    unfold blockFourierCoefficient
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [coeffs_congr_of_eqOn hF L _ (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)]

theorem coeffs_eq_zero_of_eqOn {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : ∀ k ∈ unitaryCompact ℝ N, F k = 0) :
    ∀ (L : List (Slot N)) (k : Langlands.GeneralLinear N ℝ), k ∈ unitaryCompact ℝ N →
      coeffs L F k = 0
  | [], k, hk => hF k hk
  | s :: L, _k, hk => blockFourierCoefficient_eq_zero_of s.j fun θ =>
      coeffs_eq_zero_of_eqOn hF L _ (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)

theorem norm_coeffs_le_of_mem {F : Langlands.GeneralLinear N ℝ → ℂ} {A : ℝ}
    (hA : ∀ k ∈ unitaryCompact ℝ N, ‖F k‖ ≤ A) :
    ∀ (L : List (Slot N)) (k : Langlands.GeneralLinear N ℝ), k ∈ unitaryCompact ℝ N →
      ‖coeffs L F k‖ ≤ (2 * Real.pi) ^ L.length * A
  | [], k, hk => by simpa [coeffs] using hA k hk
  | s :: L, k, hk => by
    have := norm_blockFourierCoefficient_le s.j (f := coeffs L F) (g := k)
      (B := (2 * Real.pi) ^ L.length * A) fun θ =>
        norm_coeffs_le_of_mem hA L _ (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)
    simp only [coeffs, List.length_cons]
    calc _ ≤ 2 * Real.pi * ((2 * Real.pi) ^ L.length * A) := this
      _ = (2 * Real.pi) ^ (L.length + 1) * A := by ring

/-- Right `O(N)`-invariance passes to iterated coefficients. -/
theorem coeffs_mul_mem {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : ∀ g, ∀ k ∈ unitaryCompact ℝ N, F (g * k) = F g) (L : List (Slot N))
    (g : Langlands.GeneralLinear N ℝ) {k : Langlands.GeneralLinear N ℝ}
    (hk : k ∈ unitaryCompact ℝ N) : coeffs L F (g * k) = coeffs L F g := by
  rw [coeffs_mul_right]
  congr 1
  funext y
  exact hF y k hk

/-! ## Parseval along one block -/

theorem sum_Icc_eq_of_vanish {f : ℤ → ℂ} {D E : ℕ} (hDE : D ≤ E)
    (hf : ∀ j : ℤ, (D : ℤ) < |j| → f j = 0) :
    ∑ j ∈ Finset.Icc (-(D : ℤ)) D, f j = ∑ j ∈ Finset.Icc (-(E : ℤ)) E, f j := by
  refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => hf j ?_)
  · rw [Finset.mem_Icc] at hj ⊢
    omega
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rw [lt_abs]
    omega

/-- Fourier expansion on `O(N)` with a prescribed degree bound. -/
theorem eq_sum_of_degree {p : ℕ} (hp : p + 1 < N) {u : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : Continuous u) (hK : IsKFin u) {D : ℕ}
    (hD : ∀ j : ℤ, (D : ℤ) < |j| → ∀ k ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j u k = 0)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) (θ : ℝ) :
    u (blockRotation N p θ * k) = (2 * (Real.pi : ℂ))⁻¹ *
      ∑ j ∈ Finset.Icc (-(D : ℤ)) D, blockFourierCoefficient N p j u k * expMode j θ := by
  obtain ⟨D', hD', hsum⟩ := exists_eq_sum_blockFourierCoefficient hp hu hK
  rw [hsum k hk θ,
    sum_Icc_eq_of_vanish (le_max_right D D') fun j hj => by rw [hD' j hj k hk, zero_mul],
    sum_Icc_eq_of_vanish (le_max_left D D') fun j hj => by rw [hD j hj k hk, zero_mul]]

/-- **Parseval along one block.** -/
theorem integral_mul_eq_sum (p : ℕ) {u h : Langlands.GeneralLinear N ℝ → ℂ} (hh : Continuous h)
    {D : ℕ} {k g : Langlands.GeneralLinear N ℝ}
    (hu : ∀ θ : ℝ, u (blockRotation N p θ * k) = (2 * (Real.pi : ℂ))⁻¹ *
      ∑ j ∈ Finset.Icc (-(D : ℤ)) D, blockFourierCoefficient N p j u k * expMode j θ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, u (blockRotation N p θ * k) * h (blockRotation N p θ * g) =
      (2 * (Real.pi : ℂ))⁻¹ * ∑ j ∈ Finset.Icc (-(D : ℤ)) D,
        blockFourierCoefficient N p j u k * blockFourierCoefficient N p (-j) h g := by
  have hc : Continuous fun θ : ℝ => h (blockRotation N p θ * g) :=
    hh.comp ((continuous_blockRotation N p).mul continuous_const)
  simp_rw [hu, Finset.mul_sum, Finset.sum_mul]
  have hint : ∀ j ∈ Finset.Icc (-(D : ℤ)) D, IntervalIntegrable (fun θ : ℝ =>
      (2 * (Real.pi : ℂ))⁻¹ * (blockFourierCoefficient N p j u k * expMode j θ) *
        h (blockRotation N p θ * g)) MeasureTheory.volume 0 (2 * Real.pi) := fun j _ =>
    (((continuous_const.mul (continuous_const.mul (continuous_expMode j))).mul hc)).intervalIntegrable
      _ _
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ θ : ℝ, (2 * (Real.pi : ℂ))⁻¹ * (blockFourierCoefficient N p j u k * expMode j θ) *
      h (blockRotation N p θ * g) = ((2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient N p j u k) *
        (h (blockRotation N p θ * g) *
          Complex.exp (-(((-j : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) := by
    intro θ
    simp only [expMode, Int.cast_neg, neg_mul, neg_neg]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  unfold blockFourierCoefficient
  ring

/-! ## Parseval along several blocks -/

/-- `u` has Fourier degree at most `D` on `O(N)` along every block of the list. -/
def HasDegree (slots : List (Slot N)) (D : ℕ) (u : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  ∀ s ∈ slots, ∀ j : ℤ, (D : ℤ) < |j| → ∀ k ∈ unitaryCompact ℝ N,
    blockFourierCoefficient N s.p j u k = 0

/-- **Parseval along several blocks.** For `k ∈ O(N)` and `u` continuous, right
`O(N)`-finite of degree at most `D` along the blocks,
`∫_T u(τ k) h(τ g) dτ = (2π)^{-r} Σ_J coeffs_J u (k) · coeffs_{-J} h (g)`. -/
theorem coeffs_zeroModes_mul_eq_sum (D : ℕ) : ∀ (slots : List (Slot N)),
    slots.Pairwise Slot.Disjoint →
    ∀ {u h : Langlands.GeneralLinear N ℝ → ℂ}, Continuous u → IsKFin u → HasDegree slots D u →
      Continuous h → ∀ k ∈ unitaryCompact ℝ N, ∀ g : Langlands.GeneralLinear N ℝ,
        coeffs (zeroModes slots) (fun x => u (x * k) * h (x * g)) 1 =
          (2 * (Real.pi : ℂ))⁻¹ ^ slots.length * ∑ J ∈ modeLists D slots.length,
            coeffs (withModes slots J) u k * coeffs (withModes slots (J.map Neg.neg)) h g
  | [], _, u, h, _, _, _, _, k, _, g => by
    simp [coeffs, zeroModes, withModes, modeLists]
  | s :: rest, hpw, u, h, hu, hK, hdeg, hh, k, hk, g => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hsd' : ∀ t ∈ rest, s.p + 1 < t.p ∨ t.p + 1 < s.p := hsd
    have hdeg' : HasDegree rest D u := fun t ht => hdeg t (List.mem_cons_of_mem _ ht)
    -- the inner sum at the rotated points
    have inner : ∀ θ : ℝ,
        coeffs (zeroModes rest) (fun x => u (x * k) * h (x * g)) (blockRotation N s.p θ) =
          (2 * (Real.pi : ℂ))⁻¹ ^ rest.length * ∑ J ∈ modeLists D rest.length,
            coeffs (withModes rest J) u (blockRotation N s.p θ * k) *
              coeffs (withModes rest (J.map Neg.neg)) h (blockRotation N s.p θ * g) := by
      intro θ
      rw [← one_mul (blockRotation N s.p θ), coeffs_mul_right, one_mul]
      have e : (fun y => u (y * blockRotation N s.p θ * k) * h (y * blockRotation N s.p θ * g)) =
          fun y => u (y * (blockRotation N s.p θ * k)) * h (y * (blockRotation N s.p θ * g)) := by
        funext y
        rw [mul_assoc, mul_assoc]
      rw [e]
      exact coeffs_zeroModes_mul_eq_sum D rest hrest hu hK hdeg' hh _
        (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk) _
    -- disjointness of `s` from the slots with modes
    have hdJ : ∀ J : List ℤ, ∀ t ∈ withModes rest J, s.p + 1 < t.p ∨ t.p + 1 < s.p := by
      intro J t ht
      obtain ⟨t', ht', j', rfl⟩ := mem_withModes ht
      exact hsd' t' ht'
    -- the one-block Parseval for each `J`
    have one : ∀ J : List ℤ,
        ∫ θ in (0 : ℝ)..2 * Real.pi, coeffs (withModes rest J) u (blockRotation N s.p θ * k) *
          coeffs (withModes rest (J.map Neg.neg)) h (blockRotation N s.p θ * g) =
        (2 * (Real.pi : ℂ))⁻¹ * ∑ j ∈ Finset.Icc (-(D : ℤ)) D,
          coeffs (withModes (s :: rest) (j :: J)) u k *
            coeffs (withModes (s :: rest) ((j :: J).map Neg.neg)) h g := by
      intro J
      refine integral_mul_eq_sum s.p (continuous_coeffs hh _) fun θ => ?_
      refine eq_sum_of_degree s.hp (continuous_coeffs hu _) (isKFin_coeffs hu hK _) ?_ hk θ
      intro j hj k' hk'
      rw [blockFourierCoefficient_coeffs j hu _ (hdJ J)]
      exact coeffs_eq_zero_of_eqOn (fun k'' hk'' => hdeg s List.mem_cons_self j hj k'' hk'')
        _ k' hk'
    show blockFourierCoefficient N s.p 0
      (coeffs (zeroModes rest) (fun x => u (x * k) * h (x * g))) 1 = _
    unfold blockFourierCoefficient
    simp only [mul_one, Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero]
    simp_rw [inner]
    have hint : ∀ J ∈ modeLists D rest.length, IntervalIntegrable (fun θ : ℝ =>
        coeffs (withModes rest J) u (blockRotation N s.p θ * k) *
          coeffs (withModes rest (J.map Neg.neg)) h (blockRotation N s.p θ * g))
        MeasureTheory.volume 0 (2 * Real.pi) := fun J _ =>
      ((continuous_coeffs hu _).comp ((continuous_blockRotation N s.p).mul continuous_const)).mul
        ((continuous_coeffs hh _).comp ((continuous_blockRotation N s.p).mul continuous_const))
        |>.intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hint]
    simp_rw [one]
    rw [List.length_cons, sum_modeLists_succ, Finset.sum_comm, pow_succ, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    ring

/-! ## Torus averages of tied exponential functions -/

/-- `I(x, y, w) = ∫₀^{2π} |Z(θ)|⁻¹ dθ`. -/
def invIntegral (x y w : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi, ‖rotZ x y w θ‖⁻¹

theorem continuous_inv_norm_rotZ (x y w : ℝ) : Continuous fun θ => ‖rotZ x y w θ‖⁻¹ :=
  (continuous_rotZ x y w).norm.inv₀ fun θ => norm_ne_zero_iff.mpr (rotZ_ne_zero x y w θ)

theorem norm_wave_le (u w : ℂ) (θ : ℝ) :
    ‖RealInducedBlockContour.wave u w θ‖ ≤ ‖u‖ + ‖w‖ := by
  unfold RealInducedBlockContour.wave
  have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have h2 : ‖Complex.exp (-((θ : ℂ) * Complex.I))‖ = 1 := by
    rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  calc _ ≤ ‖u * Complex.exp ((θ : ℂ) * Complex.I)‖ +
        ‖w * Complex.exp (-((θ : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = ‖u‖ + ‖w‖ := by rw [norm_mul, norm_mul, h1, h2, mul_one, mul_one]

theorem norm_rotZ_lt (x y w θ : ℝ) : ‖rotZ x y w θ‖ < 2 * ‖waveU x y w‖ := by
  rw [rotZ_eq_wave]
  have := norm_waveW_lt x y w
  linarith [norm_wave_le (waveU x y w) (waveW x y w) θ]

/-- `I(x, y, w) ≥ π / |u|`. -/
theorem pi_div_le_invIntegral (x y w : ℝ) : Real.pi / ‖waveU x y w‖ ≤ invIntegral x y w := by
  have hu := norm_waveU_pos x y w
  have hle : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (2 * ‖waveU x y w‖)⁻¹ ≤ ‖rotZ x y w θ‖⁻¹ :=
    fun θ _ => inv_anti₀ (norm_pos_iff.mpr (rotZ_ne_zero x y w θ)) (norm_rotZ_lt x y w θ).le
  have := intervalIntegral.integral_mono_on Real.two_pi_pos.le
    (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (2 * ‖waveU x y w‖)⁻¹))
    ((continuous_inv_norm_rotZ x y w).intervalIntegrable _ _) hle
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
  unfold invIntegral
  calc Real.pi / ‖waveU x y w‖ = 2 * Real.pi * (2 * ‖waveU x y w‖)⁻¹ := by
        field_simp
    _ ≤ _ := this

theorem invIntegral_pos (x y w : ℝ) : 0 < invIntegral x y w :=
  lt_of_lt_of_le (div_pos Real.pi_pos (norm_waveU_pos x y w)) (pi_div_le_invIntegral x y w)

/-- **Torus averages at `point slots`.** For `E` continuous, right `O(N)`-invariant and block
covariant with exponents `(σ_s, σ_s - 1)` at every slot,
`∫_T E(τ b_1 ⋯ b_r) dτ = ∏_s e^{σ_s (x_s + y_s)} I(x_s, y_s, w_s) · E(1)`. -/
theorem coeffs_zeroModes_point (σ : Slot N → ℂ) {E : Langlands.GeneralLinear N ℝ → ℂ}
    (hE : Continuous E) (hK : ∀ g, ∀ k ∈ unitaryCompact ℝ N, E (g * k) = E g) :
    ∀ slots : List (Slot N), slots.Pairwise Slot.Disjoint →
      (∀ s ∈ slots, IsBlockCovariant s.hp (σ s) (σ s - 1) E) →
      coeffs (zeroModes slots) E (point slots) =
        (slots.map fun s => Complex.exp (σ s * ((s.x : ℂ) + s.y)) *
          (invIntegral s.x s.y s.w : ℂ)).prod * E 1
  | [], _, _ => by simp [coeffs, zeroModes, point]
  | s :: rest, hpw, hcov => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hsd' : ∀ t ∈ rest, s.p + 1 < t.p ∨ t.p + 1 < s.p := hsd
    have hsdZ : ∀ t ∈ zeroModes rest, s.p + 1 < t.p ∨ t.p + 1 < s.p := by
      intro t ht
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      exact hsd' t' ht'
    have IH := coeffs_zeroModes_point σ hE hK rest hrest fun t ht =>
      hcov t (List.mem_cons_of_mem _ ht)
    set F := coeffs (zeroModes rest) E with hFdef
    have hFcov : IsBlockCovariant s.hp (σ s) (σ s - 1) F :=
      isBlockCovariant_coeffs s.hp (hcov s List.mem_cons_self) _ hsdZ
    have hFK : ∀ g, ∀ k ∈ unitaryCompact ℝ N, F (g * k) = F g := fun g k hk =>
      coeffs_mul_mem hK _ g hk
    have key : ∀ θ : ℝ, F (blockRotation N s.p θ * (blockB s.hp s.x s.y s.w * point rest)) =
        Complex.exp (σ s * ((s.x : ℂ) + s.y)) *
          ((‖rotZ s.x s.y s.w θ‖⁻¹ : ℝ) : ℂ) * F (point rest) := by
      intro θ
      rw [apply_blockRotation_mul_blockB s.hp hFcov,
        blockRotation_mul_point s.hp _ rest hsd',
        hFK _ _ (blockRotation_mem_unitaryCompact N s.p _)]
      have hρ : 0 < ‖rotZ s.x s.y s.w θ‖ := norm_pos_iff.mpr (rotZ_ne_zero _ _ _ θ)
      congr 1
      have e : σ s * (((s.x + s.y - Real.log ‖rotZ s.x s.y s.w θ‖ : ℝ)) : ℂ) +
          (σ s - 1) * ((Real.log ‖rotZ s.x s.y s.w θ‖ : ℝ) : ℂ) =
          σ s * ((s.x : ℂ) + s.y) - ((Real.log ‖rotZ s.x s.y s.w θ‖ : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e, Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hρ, div_eq_mul_inv,
        Complex.ofReal_inv]
    show blockFourierCoefficient N s.p 0 F (blockB s.hp s.x s.y s.w * point rest) = _
    unfold blockFourierCoefficient
    simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    simp_rw [key]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, IH]
    simp only [List.map_cons, List.prod_cons, invIntegral]
    ring

/-! ## The core bound -/

/-- The constant of the core bound. -/
def coreConst (r D : ℕ) : ℝ :=
  ((2 * D + 1 : ℝ) * ((2 : ℝ) ^ (3 * D) * (2 * D + 1) * (2 * Real.pi))) ^ r

theorem coreConst_nonneg (r D : ℕ) : 0 ≤ coreConst r D := by
  unfold coreConst
  positivity

/-- **Core bound.** For `k ∈ O(N)`, `u` continuous, right `O(N)`-finite of degree `≤ D` with
`|u| ≤ A` on `O(N)`, and `h` in `InClass slots D` with `|h| ≤ B` on `O(N)`:
`|∫_T u(τ k) h(τ b_1 ⋯ b_r k') dτ| ≤ coreConst r D · A · B · expBound slots`. -/
theorem norm_coeffs_zeroModes_le (D : ℕ) {slots : List (Slot N)}
    (hpw : slots.Pairwise Slot.Disjoint) {u h : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : Continuous u) (huK : IsKFin u) (hdeg : HasDegree slots D u) {A : ℝ}
    (hA : ∀ k ∈ unitaryCompact ℝ N, ‖u k‖ ≤ A) (hh : InClass slots D h) {B : ℝ}
    (hB : ∀ k ∈ unitaryCompact ℝ N, ‖h k‖ ≤ B) {k k' : Langlands.GeneralLinear N ℝ}
    (hk : k ∈ unitaryCompact ℝ N) (hk' : k' ∈ unitaryCompact ℝ N) :
    ‖coeffs (zeroModes slots) (fun x => u (x * k) * h (x * (point slots * k'))) 1‖ ≤
      coreConst slots.length D * A * B * expBound slots := by
  rw [coeffs_zeroModes_mul_eq_sum D slots hpw hu huK hdeg hh.1 k hk]
  set r := slots.length
  set c : ℝ := (2 : ℝ) ^ (3 * D) * (2 * D + 1) * (2 * Real.pi) with hc
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1 (one_mem _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 (one_mem _))
  have hE0 : 0 ≤ expBound slots := by
    unfold expBound
    exact List.prod_nonneg fun x hx => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
      exact div_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hterm : ∀ J ∈ modeLists D r,
      ‖coeffs (withModes slots J) u k * coeffs (withModes slots (J.map Neg.neg)) h
        (point slots * k')‖ ≤ (2 * Real.pi) ^ r * A * (c ^ r * B * expBound slots) := by
    intro J hJ
    obtain ⟨hl, hb⟩ := mem_modeLists hJ
    have hl' : (J.map Neg.neg).length = slots.length := by rw [List.length_map, hl]
    have hb' : ∀ j ∈ J.map Neg.neg, |j| ≤ D := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      rw [abs_neg]
      exact hb i hi
    rw [norm_mul]
    have h1 := norm_coeffs_le_of_mem hA (withModes slots J) k hk
    rw [length_withModes slots J hl] at h1
    have h2 := norm_coeffs_point_mul_le D (withModes slots (J.map Neg.neg))
      (pairwise_withModes _ hpw) h B (inClass_withModes hh _) hB k' hk'
    rw [point_withModes _ _ hl', expBound_withModes _ _ hl'] at h2
    have h3 := const_withModes_le D slots (J.map Neg.neg) hl' hb'
    have h4 : ‖coeffs (withModes slots (J.map Neg.neg)) h (point slots * k')‖ ≤
        c ^ r * B * expBound slots :=
      h2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hB0) hE0)
    exact mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
  calc _ = ‖(2 * (Real.pi : ℂ))⁻¹‖ ^ r * ‖∑ J ∈ modeLists D r,
        coeffs (withModes slots J) u k * coeffs (withModes slots (J.map Neg.neg)) h
          (point slots * k')‖ := by rw [norm_mul, norm_pow]
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ ^ r * ∑ J ∈ modeLists D r,
        (2 * Real.pi) ^ r * A * (c ^ r * B * expBound slots) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = coreConst r D * A * B * expBound slots := by
        have hπ : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
          rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
            Complex.norm_two]
        rw [hπ, Finset.sum_const, card_modeLists, nsmul_eq_mul, coreConst, ← hc]
        have h2π : (2 * Real.pi)⁻¹ ^ r * (2 * Real.pi) ^ r = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
        calc _ = (2 * Real.pi)⁻¹ ^ r * (2 * Real.pi) ^ r *
              (((2 * D + 1) * c) ^ r * A * B * expBound slots) := by
              rw [mul_pow (2 * (D : ℝ) + 1) c r]
              push_cast
              ring
          _ = _ := by rw [h2π, one_mul]

end RealInducedTorusCore

end Langlands.Archimedean
