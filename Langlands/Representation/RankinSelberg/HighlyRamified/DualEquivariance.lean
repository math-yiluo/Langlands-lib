import Langlands.Representation.RankinSelberg.HighlyRamified.DualFactor
import Langlands.Representation.RankinSelberg.HighlyRamified.FirstColumnLine

/-!
# Equivariance of the dual Whittaker factor under the first-column line subgroup

For `W` right invariant under the level-`f` subgroup and with central character `ω`, the
function `Ξ(A) = W(M(diag(A,1)))` on `GL_(m+1)` satisfies `Ξ(A k) = ω(k₀₀)⁻¹ Ξ(A)` for
`k ∈ K⁰(f)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix Langlands.GeneralLinear

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- Membership of `k` in the first-column line subgroup at level `f`. -/
abbrev InFirstColumn (f : ℕ) (k : GeneralLinearGroup (Fin (m + 1)) F) : Prop :=
  k ∈ firstColumnCongruence (ValuativeRel.valuation F).integer m
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f)

theorem integer_of_mem_pow {f : ℕ} {x : F}
    (hx : ∃ y : (ValuativeRel.valuation F).integer,
      y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (y : F) = x) :
    x ∈ (ValuativeRel.valuation F).integer := by
  obtain ⟨y, -, rfl⟩ := hx
  exact y.property

/-- For `k ∈ K⁰(f)` with `f ≥ 1`, the entry `k₀₀` is an integral unit and
`(k⁻¹)₀₀ k₀₀ ≡ 1` modulo `𝔭^f`. -/
theorem firstColumn_entry_unit {f : ℕ} {k : GeneralLinearGroup (Fin (m + 1)) F}
    (hk : InFirstColumn f k) :
    ∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (x : F) = (k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) 0 0 * k 0 0 - 1 := by
  obtain ⟨hint, hinv, hcol⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k).1 hk
  have hprod : ((k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) *
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) 0 0 = 1 := by
    rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one,
      Matrix.one_apply_eq]
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at hprod
  -- the remaining sum lies in 𝔭^f
  classical
  have hrest : ∀ l ∈ (Finset.univ.erase (0 : Fin (m + 1))),
      ∃ y : (ValuativeRel.valuation F).integer,
        y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
          (y : F) = (k⁻¹ : GeneralLinearGroup (Fin (m + 1)) F) 0 l * k l 0 := by
    intro l hl
    obtain ⟨y, hy, hye⟩ := hcol l (Finset.ne_of_mem_erase hl)
    refine ⟨⟨_, hinv 0 l⟩ * y, Ideal.mul_mem_left _ _ hy, ?_⟩
    push_cast
    rw [hye]
  choose! y hy hye using hrest
  refine ⟨-(∑ l ∈ Finset.univ.erase (0 : Fin (m + 1)), y l), ?_, ?_⟩
  · exact neg_mem (Ideal.sum_mem _ fun l hl => hy l hl)
  · simp only [NegMemClass.coe_neg, AddSubmonoidClass.coe_finsetSum]
    rw [Finset.sum_congr rfl hye]
    linear_combination (-1 : F) * hprod

/-- For `k ∈ K⁰(f)` with `f ≥ 1`, the entry `k₀₀` is nonzero, integral, with integral inverse. -/
theorem firstColumn_entry_isUnit {f : ℕ} (hf : 0 < f) {k : GeneralLinearGroup (Fin (m + 1)) F}
    (hk : InFirstColumn f k) :
    k 0 0 ≠ 0 ∧ k 0 0 ∈ (ValuativeRel.valuation F).integer ∧
      (k 0 0)⁻¹ ∈ (ValuativeRel.valuation F).integer := by
  obtain ⟨hint, hinv, -⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k).1 hk
  obtain ⟨x, hx, hxe⟩ := firstColumn_entry_unit hk
  set a : (ValuativeRel.valuation F).integer := ⟨_, hinv 0 0⟩
  set b : (ValuativeRel.valuation F).integer := ⟨_, hint 0 0⟩
  have hab : a * b = 1 + x := by
    apply Subtype.val_injective
    simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, a, b, hxe]
    ring
  have hxm : x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer :=
    Ideal.pow_le_self hf.ne' hx
  have hunit : IsUnit (a * b) := by
    rw [hab, show (1 : (ValuativeRel.valuation F).integer) + x = 1 - (-x) by ring]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hxm))
  have hbunit : IsUnit b := isUnit_of_mul_isUnit_right hunit
  obtain ⟨u, hu⟩ := hbunit
  have hne : k 0 0 ≠ 0 := by
    intro h0
    have : (b : F) = 0 := h0
    rw [← hu] at this
    simp at this
  refine ⟨hne, hint 0 0, ?_⟩
  have : ((u⁻¹ : (ValuativeRel.valuation F).integerˣ) : F) = (k 0 0)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    have h1 := congrArg (fun y : (ValuativeRel.valuation F).integer => (y : F)) u.mul_inv
    simp only [Subring.coe_mul, Subring.coe_one] at h1
    rw [← h1, hu]
  rw [← this]
  exact (u⁻¹ : (ValuativeRel.valuation F).integerˣ).val.property

omit [ValuativeRel F] in
theorem scalar_mul_apply {n : ℕ} (z : Fˣ) (M : GeneralLinearGroup (Fin n) F) (i j : Fin n) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) z * M : GeneralLinearGroup (Fin n) F) i j =
      (z : F) * M i j := by
  change ((Matrix.scalar (Fin n) (z : F)) * (M : Matrix (Fin n) (Fin n) F)) i j = _
  simp [Matrix.scalar_apply, Matrix.diagonal_mul]

omit [ValuativeRel F] in
theorem mul_scalar_apply {n : ℕ} (z : Fˣ) (M : GeneralLinearGroup (Fin n) F) (i j : Fin n) :
    (M * Matrix.GeneralLinearGroup.scalar (Fin n) z : GeneralLinearGroup (Fin n) F) i j =
      M i j * (z : F) := by
  change ((M : Matrix (Fin n) (Fin n) F) * (Matrix.scalar (Fin n) (z : F))) i j = _
  simp [Matrix.scalar_apply, Matrix.mul_diagonal]

/-- For `k ∈ K⁰(f)`, `f ≥ 1`, the matrix `k₀₀ · M(diag(k,1))` lies in the level-`f` subgroup. -/
theorem scalar_mul_dualConj_mem_levelSubgroup {f : ℕ} (hf : 0 < f)
    {k : GeneralLinearGroup (Fin (m + 1)) F} (hk : InFirstColumn f k) :
    Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 2))
        (Units.mk0 (k 0 0) (firstColumn_entry_isUnit hf hk).1) *
      dualConj (rankInclusion 1 k) ∈ Conductor.levelSubgroup F (m + 1 + 1) f := by
  obtain ⟨hne, h00, h00inv⟩ := firstColumn_entry_isUnit hf hk
  obtain ⟨hint, hinv, -⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k).1 hk
  have hkinv : InFirstColumn f k⁻¹ := inv_mem hk
  obtain ⟨-, -, hcolinv⟩ :=
    (mem_firstColumnCongruence (ValuativeRel.valuation F).integer m _ k⁻¹).1 hkinv
  set z : Fˣ := Units.mk0 (k 0 0) hne with hz
  have hRinv : ∀ i j, (rankInclusion 1 (rankInclusion 1 k⁻¹) :
      GeneralLinearGroup (Fin (m + 1 + 2)) F) i j ∈ (ValuativeRel.valuation F).integer :=
    fun i j => rankInclusion_entry_mem_integer _ (rankInclusion_entry_mem_integer _ hinv) i j
  have hR : ∀ i j, (rankInclusion 1 (rankInclusion 1 k) :
      GeneralLinearGroup (Fin (m + 1 + 2)) F) i j ∈ (ValuativeRel.valuation F).integer :=
    fun i j => rankInclusion_entry_mem_integer _ (rankInclusion_entry_mem_integer _ hint) i j
  have hentry : ∀ i j, dualConj (rankInclusion 1 k) i j =
      (rankInclusion 1 (rankInclusion 1 k⁻¹) : GeneralLinearGroup (Fin (m + 1 + 2)) F)
        j.rev i.rev := by
    intro i j
    rw [dualConj_entry, ← map_inv, ← map_inv]
  apply mem_levelSubgroup_of_entries
  · intro i j
    rw [scalar_mul_apply, hentry]
    exact Subring.mul_mem _ h00 (hRinv _ _)
  · intro i j
    rw [_root_.mul_inv_rev, show (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 2)) z)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 2)) z⁻¹ from (map_inv _ z).symm,
      mul_scalar_apply, dualConj_inv_entry]
    have : ((z⁻¹ : Fˣ) : F) = (k 0 0)⁻¹ := by simp [hz]
    rw [this]
    exact Subring.mul_mem _ (hR _ _) h00inv
  · intro j
    rw [scalar_mul_apply, hentry, Fin.rev_last]
    have h0 : (0 : Fin (m + 1 + 2)) = ((0 : Fin (m + 1)).castSucc).castSucc := rfl
    rw [h0]
    rcases Fin.eq_castSucc_or_eq_last j.rev with ⟨b, hb⟩ | hb
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨a, ha⟩ | ha
      · rw [hb, ha, Iwasawa.rankInclusion_castSucc_castSucc,
          Iwasawa.rankInclusion_castSucc_castSucc]
        by_cases ha0 : a = 0
        · subst ha0
          have hj : j = Fin.last (m + 1 + 1) := by
            rw [← Fin.rev_rev j, hb, ha]; ext; simp
          rw [hj, Matrix.one_apply_eq]
          obtain ⟨x, hx, hxe⟩ := firstColumn_entry_unit hk
          refine ⟨x, hx, ?_⟩
          rw [hxe, hz, Units.val_mk0]
          ring
        · have hj : Fin.last (m + 1 + 1) ≠ j := by
            intro h
            apply ha0
            rw [← h, Fin.rev_last] at hb
            rw [ha] at hb
            exact Fin.castSucc_injective _ (Fin.castSucc_injective _ hb.symm)
          rw [Matrix.one_apply_ne hj, sub_zero]
          obtain ⟨y, hy, hye⟩ := hcolinv a ha0
          refine ⟨⟨_, h00⟩ * y, Ideal.mul_mem_left _ _ hy, ?_⟩
          simp only [Subring.coe_mul, hz, Units.val_mk0, hye]
      · rw [hb, ha, Iwasawa.rankInclusion_castSucc_castSucc,
          Iwasawa.rankInclusion_last_castSucc]
        have hj : Fin.last (m + 1 + 1) ≠ j := by
          intro h
          rw [← h, Fin.rev_last, ha] at hb
          exact absurd (congrArg Fin.val hb) (by simp)
        rw [Matrix.one_apply_ne hj]
        exact ⟨0, Submodule.zero_mem _, by simp⟩
    · rw [hb, Iwasawa.rankInclusion_last_castSucc]
      have hj : Fin.last (m + 1 + 1) ≠ j := by
        intro h
        rw [← h, Fin.rev_last] at hb
        exact absurd (congrArg Fin.val hb) (by simp)
      rw [Matrix.one_apply_ne hj]
      exact ⟨0, Submodule.zero_mem _, by simp⟩

/-- `Ξ(A k) = ω(k₀₀)⁻¹ Ξ(A)` for `k ∈ K⁰(f)`, `f ≥ 1`, when `W` is right invariant under the
level-`f` subgroup and has central character `ω`. -/
theorem whittaker_dualConj_firstColumn {f : ℕ} (hf : 0 < f) (ω : Fˣ →* ℂˣ)
    (W : GeneralLinearGroup (Fin (m + 1 + 2)) F → ℂ)
    (hK : ∀ g k, k ∈ Conductor.levelSubgroup F (m + 1 + 1) f → W (g * k) = W g)
    (hω : ∀ (z : Fˣ) g, W (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 2)) z * g) =
      (ω z : ℂ) * W g)
    {k : GeneralLinearGroup (Fin (m + 1)) F} (hk : InFirstColumn f k)
    (g : GeneralLinearGroup (Fin (m + 1 + 2)) F) :
    W (g * dualConj (rankInclusion 1 k)) =
      ((ω (Units.mk0 (k 0 0) (firstColumn_entry_isUnit hf hk).1) : ℂ))⁻¹ * W g := by
  set z : Fˣ := Units.mk0 (k 0 0) (firstColumn_entry_isUnit hf hk).1 with hz
  have hX := scalar_mul_dualConj_mem_levelSubgroup hf hk
  have hdec : dualConj (rankInclusion 1 k) =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 2)) z⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 2)) z * dualConj (rankInclusion 1 k)) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [hdec, ← mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, hω, hK _ _ hX,
    map_inv, Units.val_inv_eq_inv_val]

end Langlands.RankinSelberg.HighlyRamified
