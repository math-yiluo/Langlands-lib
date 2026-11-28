import Langlands.BushnellKutzko.SplitTypeJacquet.CoarseFactorization
import Langlands.BushnellKutzko.BundledJacquetCompression

/-! # The coarse contraction `diag(ϖ on the late indices, 1 on the early ones)` -/

open Matrix ValuativeRel Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {blk : ι → ℕ} {j : ℕ} {ϖ : 𝒪[F]}

/-- The diagonal entries `ϖ` on the late indices and `1` on the early ones. -/
def coarseScale (ϖ : 𝒪[F]) (blk : ι → ℕ) (j : ℕ) : ι → F :=
  fun p => if j ≤ blk p then (ϖ : F) else 1

omit [Fintype ι] [DecidableEq ι] in
theorem coarseScale_ne_zero (hϖ : Irreducible ϖ) (p : ι) : coarseScale ϖ blk j p ≠ 0 := by
  unfold coarseScale
  split_ifs
  · exact uniformizer_ne_zero' hϖ
  · exact one_ne_zero

variable (blk j) in
/-- The element `diag(ϖ on the late indices, 1 on the early ones)`. -/
def aElt (hϖ : Irreducible ϖ) : GL ι F :=
  ⟨Matrix.diagonal (coarseScale ϖ blk j), Matrix.diagonal fun p => (coarseScale ϖ blk j p)⁻¹,
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext p q
      by_cases h : p = q
      · subst h; simp [mul_inv_cancel₀ (coarseScale_ne_zero hϖ p)]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h],
    by
      rw [Matrix.diagonal_mul_diagonal]
      ext p q
      by_cases h : p = q
      · subst h; simp [inv_mul_cancel₀ (coarseScale_ne_zero hϖ p)]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]⟩

theorem coe_aElt (hϖ : Irreducible ϖ) :
    ((aElt blk j hϖ : GL ι F) : Matrix ι ι F) = Matrix.diagonal (coarseScale ϖ blk j) := rfl

variable (blk j) in
/-- The scalar `ϖ` on the late indices. -/
def lateScalar (hϖ : Irreducible ϖ) : GL (Late blk j) F :=
  ⟨Matrix.diagonal fun _ => (ϖ : F), Matrix.diagonal fun _ => (ϖ : F)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (uniformizer_ne_zero' hϖ),
      Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (uniformizer_ne_zero' hϖ),
      Matrix.diagonal_one]⟩

theorem coarseReindex_aElt (hϖ : Irreducible ϖ) :
    coarseReindex F blk j (aElt blk j hϖ) = leviHom (lateScalar blk j hϖ, 1) := by
  ext1
  rw [coe_coarseReindex_apply, coe_leviHom]
  ext a b
  rcases a with ⟨p, hp⟩ | ⟨p, hp⟩ <;> rcases b with ⟨q, hq⟩ | ⟨q, hq⟩
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inl,
      fromBlocks_apply₁₁, coe_aElt, lateScalar]
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : p = q
    · subst h; simp [coarseScale, hp]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (congrArg Subtype.val h'))]
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, fromBlocks_apply₁₂, coe_aElt, Matrix.zero_apply]
    rw [Matrix.diagonal_apply_ne _ (fun h => hq (by rw [← h]; exact hp))]
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, fromBlocks_apply₂₁, coe_aElt, Matrix.zero_apply]
    rw [Matrix.diagonal_apply_ne _ (fun h => hp (by rw [h]; exact hq))]
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inr,
      fromBlocks_apply₂₂, coe_aElt, Units.val_one]
    rw [Matrix.diagonal_apply]
    by_cases h : p = q
    · subst h; simp [coarseScale, hp]
    · rw [ite_eq_right h, Matrix.one_apply_ne (fun h' => h (congrArg Subtype.val h'))]

theorem aElt_mem_coarseM (hϖ : Irreducible ϖ) : aElt blk j hϖ ∈ coarseM F blk j :=
  ⟨(lateScalar blk j hϖ, 1), (coarseReindex_aElt hϖ).symm⟩

theorem aElt_conj_upper (hϖ : Irreducible ϖ) (Y : Matrix (Late blk j) (Early blk j) F) :
    aElt blk j hϖ * (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Y)) *
        (aElt blk j hϖ)⁻¹ =
      (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd ((ϖ : F) • Y))) := by
  apply (coarseReindex F blk j).injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    coarseReindex_aElt, leviHom_conj_upperHom]
  congr 2
  ext a b
  simp [lateScalar, Matrix.diagonal_mul]

theorem aElt_inv_conj_lower (hϖ : Irreducible ϖ) (X : Matrix (Early blk j) (Late blk j) F) :
    (aElt blk j hϖ)⁻¹ * (coarseReindex F blk j).symm (lowerHom (Multiplicative.ofAdd X)) *
        aElt blk j hϖ =
      (coarseReindex F blk j).symm (lowerHom (Multiplicative.ofAdd ((ϖ : F) • X))) := by
  apply (coarseReindex F blk j).injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    coarseReindex_aElt]
  have hinv : (leviHom (lateScalar blk j hϖ, (1 : GL (Early blk j) F)))⁻¹ =
      leviHom ((lateScalar blk j hϖ)⁻¹, 1) := by rw [← map_inv]; rfl
  rw [hinv, show leviHom (lateScalar blk j hϖ, (1 : GL (Early blk j) F)) =
      (leviHom ((lateScalar blk j hϖ)⁻¹, (1 : GL (Early blk j) F)))⁻¹ by
    rw [← map_inv]; simp, leviHom_conj_lowerHom]
  congr 2
  ext a b
  simp [lateScalar, Matrix.mul_diagonal, mul_comm]

theorem aElt_inv_conj_levi (hϖ : Irreducible ϖ) {m : GL ι F} (hm : m ∈ coarseM F blk j) :
    (aElt blk j hϖ)⁻¹ * m * aElt blk j hϖ = m := by
  obtain ⟨⟨A, D⟩, hAD⟩ := hm
  have hAD' : coarseReindex F blk j m = leviHom (A, D) := hAD.symm
  apply (coarseReindex F blk j).injective
  rw [map_mul, map_mul, map_inv, coarseReindex_aElt, hAD', ← map_inv, ← map_mul, ← map_mul]
  congr 1
  simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_one, one_mul, mul_one, Prod.mk.injEq, and_true]
  ext1
  ext a b
  simp [lateScalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (ϖ : F)⁻¹, mul_assoc,
    mul_inv_cancel₀ (uniformizer_ne_zero' hϖ)]

theorem aElt_pow_conj_upper (hϖ : Irreducible ϖ) (r : ℕ)
    (Y : Matrix (Late blk j) (Early blk j) F) :
    aElt blk j hϖ ^ r * (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Y)) *
        (aElt blk j hϖ ^ r)⁻¹ =
      (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd ((ϖ : F) ^ r • Y))) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 : aElt blk j hϖ ^ (r + 1) *
        (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Y)) *
          (aElt blk j hϖ ^ (r + 1))⁻¹ =
        aElt blk j hϖ * (aElt blk j hϖ ^ r *
          (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Y)) *
            (aElt blk j hϖ ^ r)⁻¹) * (aElt blk j hϖ)⁻¹ := by group
    rw [e1, ih, aElt_conj_upper, smul_smul, pow_succ']

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_pow_mul_lt_one (hϖ : Irreducible ϖ) (c : F) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → valuation F ((ϖ : F) ^ s * c) < 1 := by
  by_cases hc : c = 0
  · exact ⟨0, fun s _ => by simp [hc]⟩
  obtain ⟨t, w, hw⟩ := exists_eq_zpow_mul_unit hϖ hc
  refine ⟨(1 - t).toNat, fun s hs => ?_⟩
  have hn : ((s : ℤ) + t).toNat ≥ 1 := by omega
  set n := ((s : ℤ) + t).toNat with hn'
  have hpow : (ϖ : F) ^ s * c = (ϖ : F) * ((ϖ : F) ^ (n - 1) * ((w : 𝒪[F]) : F)) := by
    rw [hw, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ (uniformizer_ne_zero' hϖ),
      ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, ← zpow_natCast]
    congr 2
    omega
  rw [hpow]
  refine val_uniformizer_mul_lt_one hϖ ?_
  rw [map_mul, map_pow]
  exact mul_le_one' (pow_le_one' (val_uniformizer_lt_one hϖ).le _) (w : 𝒪[F]).2

/-- `diag(ϖ on the late indices, 1 on the early ones)` is a compression contraction for `J1`
relative to the coarse parabolic. -/
theorem coarse_isCompressionContraction (hϖ : Irreducible ϖ)
    (K : OpenSubgroup (GL ι F)) (hKJ : K.toSubgroup = J1 F blk) :
    IsCompressionContraction K (coarseN F blk j) (coarseM F blk j) (coarseNbar F blk j)
      (aElt blk j hϖ) := by
  have hJK : ∀ x, x ∈ K ↔ x ∈ J1 F blk := fun x => by
    change x ∈ K.toSubgroup ↔ _; rw [hKJ]
  have hJK' : ∀ x, x ∈ K.toSubgroup ↔ x ∈ J1 F blk := hJK
  refine ⟨aElt_mem_coarseM hϖ, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hkJ := (hJK k).mp hk
    obtain ⟨l, ⟨hl1, hl2⟩, m, ⟨_, hm2⟩, u, ⟨hu1, hu2⟩, hlmu⟩ :=
      coarse_factor (j := j) (J1_le_J0 hkJ)
    have hmJ : m ∈ J1 F blk := by
      have : m = l⁻¹ * k * u⁻¹ := by rw [hlmu]; group
      rw [this]
      exact (J1 F blk).mul_mem ((J1 F blk).mul_mem ((J1 F blk).inv_mem hl1) hkJ)
        ((J1 F blk).inv_mem hu1)
    exact ⟨l, ⟨(hJK' l).mpr hl1, hl2⟩, m, ⟨(hJK' m).mpr hmJ, hm2⟩, u,
      ⟨(hJK' u).mpr hu1, hu2⟩, hlmu⟩
  · rintro u ⟨hu1, ⟨Y, hY⟩⟩
    have hYint : ∀ a b, valuation F (Multiplicative.toAdd Y a b) ≤ 1 := by
      intro a b
      rw [upper_entry (Y := Multiplicative.toAdd Y) hY]
      exact (((hJK' u).mp hu1).1.1 _ _).1
    have hu : u = (coarseReindex F blk j).symm (upperHom Y) := by
      rw [hY]; simp
    rw [hu]
    have := aElt_conj_upper hϖ (Multiplicative.toAdd Y)
    simp only [ofAdd_toAdd] at this
    rw [this]
    refine ⟨(hJK' _).mpr (coarse_upper_mem_J1 fun a b => ?_),
      ⟨Multiplicative.ofAdd ((ϖ : F) • Multiplicative.toAdd Y), by simp⟩⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    exact val_uniformizer_mul_lt_one hϖ (hYint a b)
  · rintro m ⟨hm1, hm2⟩
    rw [aElt_inv_conj_levi hϖ hm2]
    exact ⟨hm1, hm2⟩
  · rintro l ⟨hl1, ⟨X, hX⟩⟩
    have hXint : ∀ a b, valuation F (Multiplicative.toAdd X a b) ≤ 1 := by
      intro a b
      rw [lower_entry (X := Multiplicative.toAdd X) hX]
      exact (((hJK' l).mp hl1).1.1 _ _).1
    have hl : l = (coarseReindex F blk j).symm (lowerHom X) := by
      rw [hX]; simp
    rw [hl]
    have := aElt_inv_conj_lower hϖ (Multiplicative.toAdd X)
    simp only [ofAdd_toAdd] at this
    rw [this]
    refine ⟨(hJK' _).mpr (coarse_lower_mem_J1 fun a b => ?_),
      ⟨Multiplicative.ofAdd ((ϖ : F) • Multiplicative.toAdd X), by simp⟩⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (val_uniformizer_mul_lt_one hϖ (hXint a b)).le
  · rintro x ⟨Y, hY⟩
    have hx : x = (coarseReindex F blk j).symm (upperHom Y) := by
      rw [hY]; simp
    have hent : ∀ ab : Late blk j × Early blk j, ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
        valuation F ((ϖ : F) ^ s * Multiplicative.toAdd Y ab.1 ab.2) < 1 :=
      fun ab => exists_pow_mul_lt_one hϖ _
    choose r hr using hent
    refine ⟨Finset.univ.sup r, ?_⟩
    rw [hx]
    have := aElt_pow_conj_upper hϖ (Finset.univ.sup r) (Multiplicative.toAdd Y)
    simp only [ofAdd_toAdd] at this
    rw [this]
    refine (hJK _).mpr (coarse_upper_mem_J1 fun a b => ?_)
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hr (a, b) _ (Finset.le_sup (f := r) (Finset.mem_univ (a, b)))

end LocalField

end Langlands.BushnellKutzko.SplitTypeJacquet
