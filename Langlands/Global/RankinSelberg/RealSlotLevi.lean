import Langlands.Global.RankinSelberg.RealSlotCore
import Langlands.Global.RankinSelberg.RealGodementCompactProfile
import Langlands.Representation.Archimedean.RealBlockLeftDerivative

/-! # The inner Levi integral along the slot open cells -/

noncomputable section

open Complex MeasureTheory
open Langlands.Archimedean
open Langlands.Archimedean.RealInducedBlockBound
open Langlands.Global.RankinSelbergGlobal.RealGodementProfiles

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

variable {N : ℕ}

namespace SlotSet

variable (S : SlotSet N)

/-- Slot coordinates extended by zero to all natural numbers. -/
def ext (x : S.starts → ℝ) (p : ℕ) : ℝ := if h : p ∈ S.starts then x ⟨p, h⟩ else 0

variable {S}

theorem ext_coe (x : S.starts → ℝ) (q : S.starts) : S.ext x q = x q := by
  simp [ext, q.2]

theorem diag_congr {A B : ℕ → Matrix (Fin 2) (Fin 2) ℝ} (h : ∀ p ∈ S.starts, A p = B p) :
    S.diag A = S.diag B := by
  ext i j
  rcases S.inSlot_or i with ⟨p, o, hi⟩ | hi
  · rw [diag_row _ hi, diag_row _ hi, h p hi.1]
  · rw [diag_row_other _ hi, diag_row_other _ hi]

theorem rot_congr {θ θ' : ℕ → ℝ} (h : ∀ p ∈ S.starts, θ p = θ' p) : S.rot θ = S.rot θ' := by
  apply Units.ext
  rw [rot, rot, diagGL_val, diagGL_val]
  exact diag_congr fun p hp => by rw [h p hp]

theorem slotVec_congr {u v u' v' : ℕ → ℝ} (hu : ∀ p ∈ S.starts, u p = u' p)
    (hv : ∀ p ∈ S.starts, v p = v' p) : S.slotVec u v = S.slotVec u' v' := by
  funext i
  rcases S.inSlot_or i with ⟨p, o, hi⟩ | hi
  · rw [slotVec_of_inSlot _ _ hi, slotVec_of_inSlot _ _ hi, hu p hi.1, hv p hi.1]
  · rw [slotVec_of_not_inSlot _ _ hi, slotVec_of_not_inSlot _ _ hi]

theorem cellExponent_congr {y y' : ℕ → ℝ} (h : ∀ p ∈ S.starts, y p = y' p) :
    S.cellExponent y = S.cellExponent y' :=
  slotVec_congr (fun p hp => by rw [h p hp]) (fun p hp => by rw [h p hp])

/-- Sums against a slot vector only see the two entries of each slot. -/
theorem sum_mul_slotVec (w : Fin N → ℂ) (u v : ℕ → ℝ) :
    ∑ i, w i * (S.slotVec u v i : ℂ) =
      ∑ q : S.starts, (w (first q.2) * (u q : ℂ) + w (second q.2) * (v q : ℂ)) := by
  classical
  have hpt : ∀ i : Fin N, (S.slotVec u v i : ℂ) =
      ∑ q : S.starts, ((if i = first q.2 then (u q : ℂ) else 0) +
        (if i = second q.2 then (v q : ℂ) else 0)) := by
    intro i
    rcases S.inSlot_or i with ⟨p, o, hi⟩ | hi
    · rw [slotVec_of_inSlot _ _ hi]
      rw [Finset.sum_eq_single ⟨p, hi.1⟩]
      · have hfs : first hi.1 ≠ second hi.1 := fun e => by
          have := congrArg Fin.val e; simp [first, second] at this
        obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
        · have h1 : i = first hi.1 := Fin.ext (by simpa [first] using hi.2)
          simp [h1, hfs]
        · have h2 : i = second hi.1 := Fin.ext (by simpa [second] using hi.2)
          simp [h2, Ne.symm hfs]
      · intro q _ hq
        have h1 : i ≠ first q.2 := fun e => hq (Subtype.ext
          (S.inSlot_unique (e ▸ inSlot_first q.2) hi).1)
        have h2 : i ≠ second q.2 := fun e => hq (Subtype.ext
          (S.inSlot_unique (e ▸ inSlot_second q.2) hi).1)
        simp [h1, h2]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [slotVec_of_not_inSlot _ _ hi]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      have h1 : i ≠ first q.2 := fun e => hi q 0 (e ▸ inSlot_first q.2)
      have h2 : i ≠ second q.2 := fun e => hi q 1 (e ▸ inSlot_second q.2)
      simp [h1, h2]
  simp_rw [hpt, Finset.mul_sum, mul_add]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_add_distrib]
  simp [mul_ite]

end SlotSet

/-! ## Exponential equivariance of standard sections -/

/-- The shifted exponents `z_i + (N - 1)/2 - i` of a standard section. -/
def shiftExp (z : Fin N → ℂ) (i : Fin N) : ℂ := z i + ((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

theorem torus_eq_matrixExpUnit (γ : Fin N → ℝ) :
    RealIwasawa.torus γ = matrixExpUnit N (Matrix.diagonal γ) := by
  apply Units.ext
  rw [RealIwasawa.torus_val, matrixExpUnit_val, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [Pi.coe_exp, Real.exp_eq_exp_ℝ]

theorem charFun_exp (e : Fin 2) (t : ℂ) (x : ℝ) :
    RealJacquetFrobenius.charFun e t (Real.exp x) = Complex.exp (t * x) := by
  unfold RealJacquetFrobenius.charFun
  rw [abs_of_pos (Real.exp_pos x), div_self (Real.exp_pos x).ne', Complex.ofReal_one, one_pow,
    one_mul, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  ring_nf

/-- For `v` upper unipotent, a standard section at `v · torus γ · g` is
`exp(Σ_i shiftExp z i · γ_i)` times its value at `g`. -/
theorem standardSection_unipotent_torus_mul {p : Fin N → Fin 2} {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ}
    (hφ : IsCompactProfile p φ) (z : Fin N → ℂ) {v : Langlands.GeneralLinear N ℝ}
    (hv : v ∈ Langlands.GeneralLinear.upperUnipotent N ℝ) (γ : Fin N → ℝ)
    (g : Langlands.GeneralLinear N ℝ) :
    standardSection z φ (v * RealIwasawa.torus γ * g) =
      Complex.exp (∑ i, shiftExp z i * (γ i : ℂ)) * standardSection z φ g := by
  have hmem := (standardSection_mem hφ z).1.1
  have hχ : ∀ (i : Fin N) (x : ℝ), realPositionCharacter (characterList p z) i
      (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = Complex.exp (z i * x) := by
    intro i x
    rw [realPositionCharacter_characterList]
    exact charFun_exp _ _ _
  have hexp := RealBlockDerivative.isExpEquivariant_of_mem_principalSeries hχ hmem
  have hconj := RealIwasawa.conjTorus_mem (-γ) ⟨v, hv⟩
  rw [neg_neg] at hconj
  have he : v * RealIwasawa.torus γ * g =
      matrixExpUnit N (Matrix.diagonal γ) *
        ((RealIwasawa.torus (-γ) * v * RealIwasawa.torus γ : Langlands.GeneralLinear N ℝ)) * g := by
    rw [← torus_eq_matrixExpUnit, RealIwasawa.torus_neg]
    group
  rw [he]
  have := hexp γ ⟨_, hconj⟩ g
  simpa [shiftExp] using this


/-! ## The inner Levi integral -/

/-- The inner Levi integral `∫ F(w_M n_M(x) g) exp(2πi Σ_q b_q x_q) dx` along the slot open
cells. -/
def leviIntegral (S : SlotSet N) (F : Langlands.GeneralLinear N ℝ → ℂ) (b : ℕ → ℝ)
    (g : Langlands.GeneralLinear N ℝ) : ℂ :=
  ∫ x : S.starts → ℝ, F (S.swapGL * S.unip (S.ext x) * g) *
    Complex.exp (((2 * Real.pi * ∑ q : S.starts, b q * x q : ℝ) : ℂ) * Complex.I)

/-- The scale factors `exp(α_{p+1} - α_p)` of the slot coordinates under the torus `α`. -/
def slotScale (α : Fin N → ℝ) (p : ℕ) : ℝ :=
  Real.exp (SlotSet.natVec α (p + 1) - SlotSet.natVec α p)

theorem slotScale_pos (α : Fin N → ℝ) (p : ℕ) : 0 < slotScale α p := Real.exp_pos _

theorem exp_neg_log_cellNorm (k : ℕ) (y : ℝ) :
    Complex.exp (-(((k : ℂ) + 1) * ((Real.log (cellNorm y) : ℝ) : ℂ))) =
      ((cellNorm y : ℝ) : ℂ)⁻¹ ^ (k + 1) := by
  have hρ := cellNorm_pos y
  rw [show -(((k : ℂ) + 1) * ((Real.log (cellNorm y) : ℝ) : ℂ)) =
    (((-(k + 1 : ℕ) * Real.log (cellNorm y)) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    show -(k + 1 : ℕ) * Real.log (cellNorm y) = ((k + 1 : ℕ) : ℝ) * Real.log (cellNorm y)⁻¹ by
      rw [Real.log_inv]; ring, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hρ)]
  push_cast
  rfl

/-- **The inner Levi integral of a standard section.** In the Iwasawa coordinates of `g`, the
inner integral is the exponential factor of the permuted torus times the core integral in
the affine slot coordinates `(x_q + c_q) s_q`. -/
theorem leviIntegral_standardSection (S : SlotSet N) {p : Fin N → Fin 2}
    {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ} (hφ : IsCompactProfile p φ) (z : Fin N → ℂ)
    (m : ℕ → ℕ) (hz : ∀ q (hq : q ∈ S.starts),
      z (SlotSet.first hq) - z (SlotSet.second hq) = m q) (b : ℕ → ℝ)
    (g : Langlands.GeneralLinear N ℝ) :
    leviIntegral S (standardSection z φ) b g =
      Complex.exp (∑ i, shiftExp z i * (RealIwasawa.alpha g (S.perm i) : ℂ)) *
        ∫ x, coreIntegrand S m (standardSection z φ)
          (S.swapGL * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ)) b
          (SlotSet.slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ))
          (slotScale (RealIwasawa.alpha g)) x := by
  rw [leviIntegral, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  set c := SlotSet.slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ)
  set α := RealIwasawa.alpha g
  set y := SlotSet.shifted (S.ext x + c) α
  obtain ⟨v, hv, he⟩ := S.swapGL_unip_mul (S.ext x) g
  have hy : ∀ q (hq : q ∈ S.starts), y q = affineCoord S c (slotScale α) x ⟨q, hq⟩ := by
    intro q hq
    simp [y, affineCoord, SlotSet.shifted, slotScale, SlotSet.ext, hq]
  simp only [coreIntegrand]
  rw [he, standardSection_unipotent_torus_mul hφ z hv]
  have hrot : S.rot (fun p => Real.arctan (SlotSet.shifted (S.ext x + c) α p)) =
      S.rot (arcVec S (affineCoord S c (slotScale α) x)) :=
    SlotSet.rot_congr fun q hq => by
      change Real.arctan (y q) = _
      rw [hy q hq]
      simp [arcVec, hq]
  rw [hrot, mul_assoc (S.rot _) S.swapGL]
  have hsum : ∑ i, shiftExp z i * ((α ∘ S.perm + S.cellExponent y) i : ℂ) =
      ∑ i, shiftExp z i * (α (S.perm i) : ℂ) +
        ∑ q : S.starts, -(((m q : ℂ) + 1) *
          ((Real.log (cellNorm (affineCoord S c (slotScale α) x q)) : ℝ) : ℂ)) := by
    simp only [Pi.add_apply, Function.comp, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [SlotSet.cellExponent, SlotSet.sum_mul_slotVec]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hzq := hz q q.2
    have hsh : shiftExp z (SlotSet.first q.2) - shiftExp z (SlotSet.second q.2) = (m q : ℂ) + 1 := by
      simp only [shiftExp, SlotSet.first, SlotSet.second] at hzq ⊢
      push_cast
      linear_combination hzq
    rw [hy q q.2]
    push_cast
    linear_combination (-((Real.log (cellNorm (affineCoord S c (slotScale α) x q)) : ℝ) : ℂ)) * hsh
  have hB : Complex.exp (∑ q : S.starts, -(((m q : ℂ) + 1) *
      ((Real.log (cellNorm (affineCoord S c (slotScale α) x q)) : ℝ) : ℂ))) =
      ∏ q : S.starts, ((cellNorm (affineCoord S c (slotScale α) x q) : ℝ) : ℂ)⁻¹ ^ (m q + 1) := by
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun q _ => exp_neg_log_cellNorm _ _
  rw [hsum, Complex.exp_add, hB]
  ring


theorem norm_standardSection_unitary_le {p : Fin N → Fin 2}
    {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ} (hφ : IsCompactProfile p φ) (z : Fin N → ℂ) :
    ∃ B : ℝ, ∀ k ∈ unitaryCompact ℝ N, ‖standardSection z φ k‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_range hφ.1).isBounded.exists_norm_le
  refine ⟨B, fun k hk => ?_⟩
  have : standardSection z φ k = φ ⟨k.val, hk⟩ := by
    have h := congrFun (compactRestriction_standardSection φ z) ⟨k.val, hk⟩
    rw [← h]
    rfl
  rw [this]
  exact hB _ (Set.mem_range_self _)

theorem isKFin_standardSection {p : Fin N → Fin 2}
    {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ} (hφ : IsCompactProfile p φ) (z : Fin N → ℂ) :
    IsKFin (standardSection z φ) :=
  (Submodule.mem_inf.mp (standardSection_mem hφ z)).2

theorem continuous_standardSection {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ} (hφ : Continuous φ)
    (z : Fin N → ℂ) : Continuous (standardSection z φ) := by
  have h := continuous_standardSection_family (n := N) hφ
  have h2 : Continuous fun g : Langlands.GeneralLinear N ℝ =>
      ((z, g) : (Fin N → ℂ) × Langlands.GeneralLinear N ℝ) :=
    continuous_const.prodMk continuous_id
  have h3 := h.comp h2
  exact h3

theorem standardSection_eq_on_unitary (φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ) (z z' : Fin N → ℂ) :
    ∀ k ∈ unitaryCompact ℝ N, standardSection z φ k = standardSection z' φ k := by
  intro k hk
  have h := congrFun (compactRestriction_standardSection φ z) ⟨k.val, hk⟩
  have h' := congrFun (compactRestriction_standardSection φ z') ⟨k.val, hk⟩
  exact h.trans h'.symm

/-- **Pointwise bound of the inner Levi integral of a standard section**, uniformly in the
exponents with the prescribed differences on the slots. -/
theorem norm_leviIntegral_le (S : SlotSet N) {p : Fin N → Fin 2}
    {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ} (hφ : IsCompactProfile p φ)
    (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0) (z₀ : Fin N → ℂ)
    (hmodes : SlotModes (slotsOf S m) (standardSection z₀ φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin N → ℂ,
      (∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q) →
      ∀ (b : ℕ → ℝ) (g : Langlands.GeneralLinear N ℝ),
      ‖leviIntegral S (standardSection z φ) b g‖ ≤
        C * Real.exp (∑ i, (shiftExp z i).re * RealIwasawa.alpha g (S.perm i)) *
          ∏ q : S.starts, ((slotScale (RealIwasawa.alpha g) q)⁻¹ *
            |b q / slotScale (RealIwasawa.alpha g) q| ^ ((m q : ℝ) / 2)) := by
  obtain ⟨B, hBK⟩ := norm_standardSection_unitary_le hφ z₀
  obtain ⟨D, hdeg⟩ := RealInducedStandardBound.exists_hasDegree
    (continuous_standardSection hφ.1 z₀) (isKFin_standardSection hφ z₀) (slotsOf S m)
  refine ⟨coreConstant S m D B, coreConstant_nonneg S m D B, fun z hz b g => ?_⟩
  have hK := standardSection_eq_on_unitary φ z₀ z
  have hk' : S.swapGL * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ) ∈
      unitaryCompact ℝ N := mul_mem S.swapGL_mem (RealIwasawa.kpart g).property
  obtain ⟨-, hbound⟩ := core_bound S m hm (continuous_standardSection hφ.1 z)
    (isKFin_standardSection hφ z) (hasDegree_congr hK hdeg) (slotModes_congr hK hmodes)
    (fun k hk => (hK k hk) ▸ hBK k hk) hk' b
    (SlotSet.slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ))
    (slotScale (RealIwasawa.alpha g)) (fun q _ => slotScale_pos _ _)
  set I := ∫ x, coreIntegrand S m (standardSection z φ)
    (S.swapGL * (RealIwasawa.kpart g : Langlands.GeneralLinear N ℝ)) b
    (SlotSet.slotCoord (RealIwasawa.npart g : Langlands.GeneralLinear N ℝ))
    (slotScale (RealIwasawa.alpha g)) x with hI
  set P := ∏ q : S.starts, ((slotScale (RealIwasawa.alpha g) q)⁻¹ *
    |b q / slotScale (RealIwasawa.alpha g) q| ^ ((m q : ℝ) / 2))
  set E := ∑ i, (shiftExp z i).re * RealIwasawa.alpha g (S.perm i)
  have hre : (∑ i, shiftExp z i * (RealIwasawa.alpha g (S.perm i) : ℂ)).re = E := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re]
  rw [leviIntegral_standardSection S hφ z m hz b g, ← hI, norm_mul, Complex.norm_exp, hre]
  have h := mul_le_mul_of_nonneg_left hbound (Real.exp_pos E).le
  calc Real.exp E * ‖I‖ ≤ Real.exp E * (coreConstant S m D B * P) := h
    _ = coreConstant S m D B * Real.exp E * P := by ring


/-! ## The exponent of the bound -/

/-- The real `ρ`-shift `(N - 1)/2 - i`. -/
def rhoShift (i : Fin N) : ℝ := ((N : ℝ) - 1) / 2 - (i : ℕ)

/-- The real parts of the exponents minus the signed slot half-weights: `m_q/2` is subtracted at
the first position of each slot `q` and added at the second. When
`Re z_{first q} - Re z_{second q} = m_q`, both values on the slot equal the average of the two real
parts. -/
def blockRe (S : SlotSet N) (m : ℕ → ℕ) (z : Fin N → ℂ) (i : Fin N) : ℝ :=
  (z i).re - S.slotVec (fun q => (m q : ℝ) / 2) (fun q => -((m q : ℝ) / 2)) i

namespace SlotSet

variable {S : SlotSet N}

theorem sum_mul_slotVec_real (w : Fin N → ℝ) (u v : ℕ → ℝ) :
    ∑ i, w i * S.slotVec u v i =
      ∑ q : S.starts, (w (first q.2) * u q + w (second q.2) * v q) := by
  have h := S.sum_mul_slotVec (fun i => (w i : ℂ)) u v
  exact_mod_cast h

end SlotSet

theorem shiftExp_perm_re (S : SlotSet N) (m : ℕ → ℕ) (z : Fin N → ℂ)
    (hz : ∀ q (hq : q ∈ S.starts), (z (SlotSet.first hq)).re - (z (SlotSet.second hq)).re = m q)
    (i : Fin N) :
    (shiftExp z (S.perm i)).re = blockRe S m z i + rhoShift i +
      S.slotVec (fun q => -(1 + (m q : ℝ) / 2)) (fun q => 1 + (m q : ℝ) / 2) i := by
  have hre : ∀ j : Fin N, (shiftExp z j).re = (z j).re + rhoShift j := by
    intro j
    simp [shiftExp, rhoShift]
    ring
  rw [hre]
  simp only [blockRe]
  rcases S.inSlot_or i with ⟨q, o, h⟩ | h
  · have hq : q ∈ S.starts := h.1
    have h' := S.inSlot_swapFun h
    rw [SlotSet.perm_apply, SlotSet.slotVec_of_inSlot _ _ h, SlotSet.slotVec_of_inSlot _ _ h]
    have hzq := hz q hq
    have hf : (SlotSet.first hq).val = q := rfl
    have hs : (SlotSet.second hq).val = q + 1 := rfl
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · have hi : i = SlotSet.first hq := Fin.ext (by simpa [SlotSet.first] using h.2)
      have hsw : S.swapFun i = SlotSet.second hq := Fin.ext (by
        simpa [SlotSet.second] using h'.2)
      rw [hsw, hi]
      simp only [rhoShift, hf, hs, ite_true]
      push_cast
      linarith
    · have hi : i = SlotSet.second hq := Fin.ext (by simpa [SlotSet.second] using h.2)
      have hsw : S.swapFun i = SlotSet.first hq := Fin.ext (by
        simpa [SlotSet.first] using h'.2)
      rw [hsw, hi]
      simp only [rhoShift, hf, hs, show (1 : Fin 2) ≠ 0 by decide, ite_false]
      push_cast
      linarith
  · rw [SlotSet.perm_apply, SlotSet.not_inSlot_swapFun h, SlotSet.slotVec_of_not_inSlot _ _ h,
      SlotSet.slotVec_of_not_inSlot _ _ h]
    ring

/-- **The exponent identity.** The permuted shifted exponents together with the slot scale
factors give the block-averaged real exponents plus `ρ`. -/
theorem levi_exponent_identity (S : SlotSet N) (m : ℕ → ℕ) (z : Fin N → ℂ)
    (hz : ∀ q (hq : q ∈ S.starts), (z (SlotSet.first hq)).re - (z (SlotSet.second hq)).re = m q)
    (α : Fin N → ℝ) :
    ∑ i, (shiftExp z i).re * α (S.perm i) +
        ∑ q : S.starts, (1 + (m q : ℝ) / 2) * (α (SlotSet.first q.2) - α (SlotSet.second q.2)) =
      ∑ i, (blockRe S m z i + rhoShift i) * α i := by
  have hσ : ∑ i, (shiftExp z i).re * α (S.perm i) = ∑ i, (shiftExp z (S.perm i)).re * α i := by
    calc ∑ i, (shiftExp z i).re * α (S.perm i)
        = ∑ i, (shiftExp z (S.perm (S.perm i))).re * α (S.perm i) := by
          simp only [SlotSet.perm_perm]
      _ = ∑ i, (shiftExp z (S.perm i)).re * α i :=
          Equiv.sum_comp S.perm (fun i => (shiftExp z (S.perm i)).re * α i)
  set sv := S.slotVec (fun q => -(1 + (m q : ℝ) / 2)) (fun q => 1 + (m q : ℝ) / 2)
  have hsplit : ∑ i, (shiftExp z (S.perm i)).re * α i =
      ∑ i, (blockRe S m z i + rhoShift i) * α i + ∑ i, α i * sv i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [shiftExp_perm_re S m z hz i]
    ring
  rw [hσ, hsplit, SlotSet.sum_mul_slotVec_real, add_assoc, ← Finset.sum_add_distrib]
  have h0 : ∀ q : S.starts, α (SlotSet.first q.2) * -(1 + (m q : ℝ) / 2) +
      α (SlotSet.second q.2) * (1 + (m q : ℝ) / 2) +
      (1 + (m q : ℝ) / 2) * (α (SlotSet.first q.2) - α (SlotSet.second q.2)) = 0 := by
    intro q; ring
  rw [Finset.sum_congr rfl fun q _ => h0 q, Finset.sum_const_zero, add_zero]

theorem slotScale_factor (α : Fin N → ℝ) (m : ℕ) (b : ℝ) {p : ℕ} (hp : p + 1 < N) :
    (slotScale α p)⁻¹ * |b / slotScale α p| ^ ((m : ℝ) / 2) =
      |b| ^ ((m : ℝ) / 2) * Real.exp ((1 + (m : ℝ) / 2) *
        (α ⟨p, by omega⟩ - α ⟨p + 1, hp⟩)) := by
  have hs := slotScale_pos α p
  have h1 : SlotSet.natVec α (p + 1) = α ⟨p + 1, hp⟩ := by simp [SlotSet.natVec, hp]
  have h0 : SlotSet.natVec α p = α ⟨p, by omega⟩ := by simp [SlotSet.natVec, show p < N by omega]
  rw [abs_div, abs_of_pos hs, Real.div_rpow (abs_nonneg _) hs.le]
  have hsr : slotScale α p ^ ((m : ℝ) / 2) =
      Real.exp ((m : ℝ) / 2 * (α ⟨p + 1, hp⟩ - α ⟨p, by omega⟩)) := by
    rw [slotScale, h1, h0, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    ring_nf
  rw [hsr, slotScale, h1, h0, ← Real.exp_neg, div_eq_mul_inv, ← Real.exp_neg]
  rw [mul_comm, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **The inner Levi integral in spherical form.** The inner Levi integral of a standard
section is bounded by a constant times `|b_q|^{m_q/2}` over the slots times the spherical
function `exp(Σ_i (λ_i + ρ_i) α_i(g))` of the block-averaged real exponents `λ`. -/
theorem norm_leviIntegral_le_spherical (S : SlotSet N) {p : Fin N → Fin 2}
    {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ} (hφ : IsCompactProfile p φ)
    (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0) (z₀ : Fin N → ℂ)
    (hmodes : SlotModes (slotsOf S m) (standardSection z₀ φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin N → ℂ,
      (∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q) →
      ∀ (b : ℕ → ℝ) (g : Langlands.GeneralLinear N ℝ),
      ‖leviIntegral S (standardSection z φ) b g‖ ≤
        C * (∏ q : S.starts, |b q| ^ ((m q : ℝ) / 2)) *
          Real.exp (∑ i, (blockRe S m z i + rhoShift i) * RealIwasawa.alpha g i) := by
  obtain ⟨C, hC, h⟩ := norm_leviIntegral_le S hφ m hm z₀ hmodes
  refine ⟨C, hC, fun z hz b g => ?_⟩
  have hzre : ∀ q (hq : q ∈ S.starts),
      (z (SlotSet.first hq)).re - (z (SlotSet.second hq)).re = m q := by
    intro q hq
    have := congrArg Complex.re (hz q hq)
    simpa using this
  set α := RealIwasawa.alpha g
  have hprod : ∏ q : S.starts, ((slotScale α q)⁻¹ * |b q / slotScale α q| ^ ((m q : ℝ) / 2)) =
      (∏ q : S.starts, |b q| ^ ((m q : ℝ) / 2)) *
        Real.exp (∑ q : S.starts, (1 + (m q : ℝ) / 2) *
          (α (SlotSet.first q.2) - α (SlotSet.second q.2))) := by
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun q _ => slotScale_factor α (m q) (b q) (S.lt q q.2)
  have hE := levi_exponent_identity S m z hzre α
  calc ‖leviIntegral S (standardSection z φ) b g‖
      ≤ C * Real.exp (∑ i, (shiftExp z i).re * α (S.perm i)) *
          ∏ q : S.starts, ((slotScale α q)⁻¹ * |b q / slotScale α q| ^ ((m q : ℝ) / 2)) :=
        h z hz b g
    _ = C * (∏ q : S.starts, |b q| ^ ((m q : ℝ) / 2)) *
          Real.exp (∑ i, (blockRe S m z i + rhoShift i) * α i) := by
        rw [hprod, ← hE, Real.exp_add]
        ring

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
