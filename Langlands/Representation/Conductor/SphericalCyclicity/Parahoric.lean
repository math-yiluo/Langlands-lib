import Langlands.Representation.Conductor.SphericalCyclicity.Cells

/-!
# The parahoric subgroup of type `(1, n + 1)` and right multiplication on the cell

The parahoric subgroup `J ⊆ GL_(n+2)(O)` consists of the integral invertible matrices
whose first-column tail lies in the maximal ideal.  We prove that its elements have a
unit head entry and a unit lower-right determinant, and that right multiplication by an
element of `J` preserves the big cell and multiplies the lower-right block by an
integral invertible matrix (by a principal congruence matrix of level `a` when the
element lies in the principal congruence subgroup of level `a ≥ 1`).
-/

noncomputable section

namespace Langlands.Conductor.SphericalCyclicity

open Matrix Langlands.GeneralLinear Langlands.Conductor
open Langlands.Conductor.UnramifiedPrincipalSeries
open scoped BigOperators

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]

set_option quotPrecheck false in
local notation "𝒱" => ValuativeRel.valuation F
set_option quotPrecheck false in
local notation "𝒪" => (ValuativeRel.valuation F).integer

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

include hϖ

/-- For a uniformizing element, valuation below one means valuation at most `v(ϖ)`. -/
theorem val_lt_one_iff_le_uniformizer (x : F) : 𝒱 x < 1 ↔ 𝒱 x ≤ 𝒱 (ϖ : F) := by
  refine ⟨fun hx => ?_, fun hx => hx.trans_lt hϖ.1⟩
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero]
    exact zero_le
  obtain ⟨m, hm⟩ := hϖ.2 x hx0
  have hanti := zpow_right_strictAnti₀ (Iwasawa.valuation_pos (ValuativeRel.valuation F) ϖ) hϖ.1
  rw [hm] at hx ⊢
  have hmpos : (0 : ℤ) < m := by
    rw [← zpow_zero (𝒱 (ϖ : F))] at hx
    exact hanti.lt_iff_gt.mp hx
  calc 𝒱 (ϖ : F) ^ m ≤ 𝒱 (ϖ : F) ^ (1 : ℤ) := hanti.antitone (by omega)
    _ = 𝒱 (ϖ : F) := zpow_one _

theorem val_inv_uniformizer_mul_le_one {x : F} (hx : 𝒱 x < 1) :
    𝒱 ((ϖ : F)⁻¹ * x) ≤ 1 := by
  have hpos := Iwasawa.valuation_pos (ValuativeRel.valuation F) ϖ
  rw [map_mul, map_inv₀]
  rw [val_lt_one_iff_le_uniformizer hϖ] at hx
  calc (𝒱 (ϖ : F))⁻¹ * 𝒱 x ≤ (𝒱 (ϖ : F))⁻¹ * 𝒱 (ϖ : F) := by gcongr
    _ = 1 := inv_mul_cancel₀ hpos.ne'

theorem val_lt_one_of_inv_uniformizer_mul_le_one {x : F} (hx : 𝒱 ((ϖ : F)⁻¹ * x) ≤ 1) :
    𝒱 x < 1 := by
  have hx' : x = (ϖ : F) * ((ϖ : F)⁻¹ * x) := by
    rw [mul_inv_cancel_left₀ ϖ.ne_zero]
  rw [hx', map_mul]
  exact mul_lt_one_of_lt_of_le hϖ.1 hx

/-- Membership in a power of the maximal ideal, in terms of the valuation. -/
theorem mem_maximalIdeal_pow_iff (a : ℕ) (x : 𝒪) :
    x ∈ IsLocalRing.maximalIdeal 𝒪 ^ a ↔ 𝒱 (x : F) ≤ 𝒱 (ϖ : F) ^ a := by
  rw [maximalIdeal_pow_eq_span_jacquetUniformizer _ ϖ hϖ a, Ideal.mem_span_singleton,
    (Valuation.integer.integers _).dvd_iff_le]
  change 𝒱 (x : F) ≤ 𝒱 (((jacquetUniformizerInteger _ ϖ hϖ ^ a : 𝒪)) : F) ↔ _
  rw [SubmonoidClass.coe_pow, map_pow]
  rfl

theorem val_uniformizer_pow_le_one (a : ℕ) : 𝒱 (ϖ : F) ^ a ≤ 1 :=
  pow_le_one₀ zero_le hϖ.1.le

/-- Membership in the principal congruence subgroup of level `a`, in terms of the
valuations of the entries of `g - 1` and `g⁻¹ - 1`. -/
theorem mem_principalLevelSubgroup_iff {m a : ℕ} (g : GL (Fin (m + 1)) F) :
    g ∈ principalLevelSubgroup F m a ↔
      (∀ i j, 𝒱 (g.val i j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) ≤ 𝒱 (ϖ : F) ^ a) ∧
      (∀ i j, 𝒱 ((g⁻¹).val i j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) ≤
        𝒱 (ϖ : F) ^ a) := by
  rw [principalLevelSubgroup, mem_principalCongruenceSubgroup_iff]
  have key : ∀ t : F, (∃ x : 𝒪, x ∈ IsLocalRing.maximalIdeal 𝒪 ^ a ∧ (x : F) = t) ↔
      𝒱 t ≤ 𝒱 (ϖ : F) ^ a := by
    intro t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_maximalIdeal_pow_iff hϖ a x).1 hx
    · intro ht
      have hmem : t ∈ 𝒪 := mem_of_val_le_one (ht.trans (val_uniformizer_pow_le_one hϖ a))
      exact ⟨⟨t, hmem⟩, (mem_maximalIdeal_pow_iff hϖ a _).2 ht, rfl⟩
  simp only [key]

/-! ### The column expansion modulo the maximal ideal -/

omit hϖ [ValuativeRel F] in
theorem val_neg_one_pow_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) (k : ℕ) (x : F) : v ((-1) ^ k * x) = v x := by
  rw [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]

omit hϖ in
/-- For an integral matrix whose first-column tail lies in the maximal ideal, the
determinant agrees with `X 0 0 * det (low X)` modulo the maximal ideal. -/
theorem val_det_sub_head_mul_lt {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hX : ∀ i j, X i j ∈ 𝒪) (hc : ∀ i, 𝒱 (colT X i) < 1) :
    𝒱 (X.det - X 0 0 * (low X).det) < 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : (-1 : F) ^ ((0 : Fin (m + 1)) : ℕ) * X 0 0 *
      (X.submatrix (Fin.succAbove 0) Fin.succ).det = X 0 0 * (low X).det := by
    simp [low, Fin.succAbove_zero]
  rw [h0, add_sub_cancel_left]
  refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
  rw [map_mul, val_neg_one_pow_mul]
  exact mul_lt_one_of_lt_of_le (hc i)
    (val_le_one_of_mem (Cartan.det_mem_integer _ fun a b => hX _ _))

/-! ### The parahoric subgroup -/

variable {n : ℕ}

/-- The parahoric subgroup `J = K ∩ t' K t'⁻¹` for `t' = diag(1, ϖ, …, ϖ)`. -/
def parahoric (ϖ : Fˣ) : Subgroup (GL (Fin (n + 2)) F) :=
  integralSubgroup 𝒪 (n + 1) ⊓
    (integralSubgroup 𝒪 (n + 1)).comap (MulAut.conj (tPrime ϖ)⁻¹).toMonoidHom

theorem integral_tPrime_conj_iff (x : GL (Fin (n + 2)) F)
    (hx : x ∈ integralSubgroup 𝒪 (n + 1)) :
    (tPrime ϖ)⁻¹ * x * tPrime ϖ ∈ integralSubgroup 𝒪 (n + 1) ↔ ∀ i, 𝒱 (colT x.val i) < 1 := by
  constructor
  · intro h i
    have hmem := integral_entry h i.succ 0
    rw [tPrime_conj_val] at hmem
    simp only [blk_succ_zero, Pi.smul_apply, smul_eq_mul] at hmem
    exact val_lt_one_of_inv_uniformizer_mul_le_one hϖ (val_le_one_of_mem hmem)
  · intro h
    apply Unramified.MinusculeCosets.mem_integralSubgroup_of_det
    · intro i j
      rw [tPrime_conj_val]
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa using integral_entry hx 0 0
      · simp only [blk_zero_succ, Pi.smul_apply, smul_eq_mul, rowT_apply]
        exact mul_mem (mem_of_val_le_one hϖ.1.le) (integral_entry hx 0 j.succ)
      · simp only [blk_succ_zero, Pi.smul_apply, smul_eq_mul]
        exact mem_of_val_le_one (val_inv_uniformizer_mul_le_one hϖ (h i))
      · simpa using integral_entry hx i.succ j.succ
    · have hdet : ((tPrime ϖ)⁻¹ * x * tPrime ϖ).val.det = x.val.det := by
        rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm (det _) (det x.val),
          mul_assoc, ← det_mul, Units.inv_mul, det_one, mul_one]
      rw [hdet]
      exact Unramified.MinusculeCosets.valuation_det_eq_one hx

theorem mem_parahoric_iff (x : GL (Fin (n + 2)) F) :
    x ∈ parahoric ϖ ↔ x ∈ integralSubgroup 𝒪 (n + 1) ∧ ∀ i, 𝒱 (colT x.val i) < 1 := by
  rw [parahoric, Subgroup.mem_inf, Subgroup.mem_comap]
  change x ∈ integralSubgroup 𝒪 (n + 1) ∧
      (tPrime ϖ)⁻¹ * x * ((tPrime ϖ)⁻¹)⁻¹ ∈ integralSubgroup 𝒪 (n + 1) ↔ _
  rw [inv_inv]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (integral_tPrime_conj_iff hϖ x hx).1 h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (integral_tPrime_conj_iff hϖ x hx).2 h⟩

/-- Elements of the parahoric subgroup have a unit head entry and a unit
lower-right determinant. -/
theorem parahoric_head {u : GL (Fin (n + 2)) F} (hu : u ∈ parahoric ϖ) :
    𝒱 (u.val 0 0) = 1 ∧ 𝒱 (low u.val).det = 1 := by
  obtain ⟨hK, hc⟩ := (mem_parahoric_iff hϖ u).1 hu
  have hdet := Unramified.MinusculeCosets.valuation_det_eq_one hK
  have hlt := val_det_sub_head_mul_lt u.val (integral_entry hK) hc
  have hprod : 𝒱 (u.val 0 0 * (low u.val).det) = 1 := by
    rw [← hdet]
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hdet]
    exact hlt
  exact val_eq_one_of_mul_eq_one (val_le_one_of_mem (integral_entry hK 0 0))
    (val_le_one_of_mem (Cartan.det_mem_integer _ fun i j => integral_entry hK _ _)) hprod

theorem isUnit_det_low_of_parahoric {u : GL (Fin (n + 2)) F} (hu : u ∈ parahoric ϖ) :
    IsUnit (low u.val).det := by
  apply isUnit_iff_ne_zero.2
  intro h0
  have := (parahoric_head hϖ hu).2
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem lowGL_mem_integral_of_parahoric {u : GL (Fin (n + 2)) F} (hu : u ∈ parahoric ϖ) :
    lowGL u ∈ integralSubgroup 𝒪 n := by
  have hK := ((mem_parahoric_iff hϖ u).1 hu).1
  have hval := lowGL_val (isUnit_det_low_of_parahoric hϖ hu)
  apply Unramified.MinusculeCosets.mem_integralSubgroup_of_det
  · intro i j
    rw [hval]
    exact integral_entry hK i.succ j.succ
  · rw [hval]
    exact (parahoric_head hϖ hu).2

theorem inCell_of_parahoric {u : GL (Fin (n + 2)) F} (hu : u ∈ parahoric ϖ) : InCell u := by
  have hc := ((mem_parahoric_iff hϖ u).1 hu).2
  have hunit := isUnit_det_low_of_parahoric hϖ hu
  have hK' := lowGL_mem_integral_of_parahoric hϖ hu
  refine ⟨hunit, fun i => ?_⟩
  have hinv : (low u.val)⁻¹ = ((lowGL u)⁻¹ : GL (Fin (n + 1)) F).val := by
    rw [Matrix.coe_units_inv, lowGL_val hunit]
  rw [cellVec, hinv]
  exact mulVec_val_lt_one (integral_entry (inv_mem hK')) hc i

theorem lowerUnip_mem_parahoric {y : Fin (n + 1) → F} (hy : ∀ i, 𝒱 (y i) < 1) :
    lowerUnip y ∈ parahoric ϖ := by
  rw [mem_parahoric_iff hϖ]
  refine ⟨?_, hy⟩
  apply Unramified.MinusculeCosets.mem_integralSubgroup_of_det
  · intro i j
    rw [lowerUnip_val]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
    · simpa using mem_of_val_le_one (hy i).le
    · simp only [blk_succ_succ]
      by_cases h : i = j
      · rw [h, Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne h]; exact zero_mem _
  · rw [det_lowerUnip, map_one]

/-! ### Right multiplication by the parahoric subgroup on the cell -/

omit hϖ [ValuativeRel F] in
theorem low_mul_lowerUnip (X : Matrix (Fin (n + 2)) (Fin (n + 2)) F) (y : Fin (n + 1) → F) :
    low (X * (lowerUnip y).val) = low X := by
  rw [low_mul]
  simp [lowerUnip_val]

omit [ValuativeRel F] hϖ in
theorem colT_mul_lowerUnip_neg_cellVec {x : GL (Fin (n + 2)) F} (hx : IsUnit (low x.val).det) :
    colT (x * lowerUnip (-cellVec x)).val = 0 := by
  rw [Units.val_mul, colT_mul, lowerUnip_val]
  simp only [blk_zero_zero, one_smul, colT_blk]
  rw [cellVec, mulVec_neg, mulVec_mulVec, Matrix.mul_nonsing_inv _ hx, one_mulVec,
    add_neg_cancel]

omit [ValuativeRel F] hϖ in
theorem lowGL_mul_lowerUnip_neg_cellVec {x : GL (Fin (n + 2)) F} (hx : IsUnit (low x.val).det) :
    lowGL (x * lowerUnip (-cellVec x)) = lowGL x := by
  have h1 : low (x * lowerUnip (-cellVec x)).val = low x.val := by
    rw [Units.val_mul, low_mul_lowerUnip]
  apply Units.ext
  rw [lowGL_val (h1 ▸ hx), lowGL_val hx, h1]

/-- Right multiplication by the parahoric subgroup preserves the cell, and the
lower-right block changes by the lower-right block of `lowerUnip (cellVec x) * k`. -/
theorem cell_mul_parahoric {x k : GL (Fin (n + 2)) F} (hx : InCell x) (hk : k ∈ parahoric ϖ) :
    InCell (x * k) ∧ lowerUnip (cellVec x) * k ∈ parahoric ϖ ∧
      lowGL (x * k) = lowGL x * lowGL (lowerUnip (cellVec x) * k) := by
  set y := cellVec x with hy
  set p := x * lowerUnip (-y) with hp
  have hpc : colT p.val = 0 := colT_mul_lowerUnip_neg_cellVec hx.1
  have hu : lowerUnip y * k ∈ parahoric ϖ :=
    mul_mem (lowerUnip_mem_parahoric hϖ hx.2) hk
  have hxk : x * k = p * (lowerUnip y * k) := by
    rw [hp, mul_assoc, ← mul_assoc (lowerUnip (-y)), lowerUnip_add, neg_add_cancel,
      lowerUnip_zero, one_mul]
  refine ⟨?_, hu, ?_⟩
  · rw [hxk, inCell_mul_iff hpc]
    exact inCell_of_parahoric hϖ hu
  · rw [hxk, lowGL_mul_of_colT_eq_zero hpc (isUnit_det_low_of_parahoric hϖ hu), hp,
      lowGL_mul_lowerUnip_neg_cellVec hx.1]

theorem inCell_of_mul_parahoric {x k : GL (Fin (n + 2)) F} (hxk : InCell (x * k))
    (hk : k ∈ parahoric ϖ) : InCell x := by
  have := (cell_mul_parahoric hϖ hxk (inv_mem hk)).1
  rwa [mul_inv_cancel_right] at this

theorem inCell_mul_parahoric_iff (x : GL (Fin (n + 2)) F) {k : GL (Fin (n + 2)) F}
    (hk : k ∈ parahoric ϖ) : InCell (x * k) ↔ InCell x :=
  ⟨fun h => inCell_of_mul_parahoric hϖ h hk, fun h => (cell_mul_parahoric hϖ h hk).1⟩

/-! ### Principal congruence elements -/

omit hϖ in
theorem integral_of_mem_principalLevel {m a : ℕ} {g : GL (Fin (m + 1)) F}
    (hg : g ∈ principalLevelSubgroup F m a) : g ∈ integralSubgroup 𝒪 m := by
  have := principalLevelSubgroup_antitone F m (Nat.zero_le a) hg
  rwa [principalLevelSubgroup_zero] at this

theorem mem_parahoric_of_principalLevel {a : ℕ} (ha : 0 < a) {k : GL (Fin (n + 2)) F}
    (hk : k ∈ principalLevelSubgroup F (n + 1) a) : k ∈ parahoric ϖ := by
  rw [mem_parahoric_iff hϖ]
  refine ⟨integral_of_mem_principalLevel hk, fun i => ?_⟩
  have h := ((mem_principalLevelSubgroup_iff hϖ k).1 hk).1 i.succ 0
  rw [Matrix.one_apply_ne (Fin.succ_ne_zero i), sub_zero] at h
  calc 𝒱 (colT k.val i) ≤ 𝒱 (ϖ : F) ^ a := h
    _ ≤ 𝒱 (ϖ : F) ^ 1 := pow_le_pow_of_le_one zero_le hϖ.1.le ha
    _ < 1 := by rw [pow_one]; exact hϖ.1

omit [ValuativeRel F] hϖ in
theorem one_succ_succ {m : ℕ} (i j : Fin (m + 1)) :
    (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) F) i.succ j.succ =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j := by
  simp [Matrix.one_apply, Fin.succ_inj]

/-- If `k` lies in the principal congruence subgroup of level `a ≥ 1` and `y` has
coordinates in the maximal ideal, then the lower-right block of `lowerUnip y * k`
lies in the principal congruence subgroup of level `a` of the smaller group. -/
theorem lowGL_lowerUnip_mul_mem_principalLevel {a : ℕ} (ha : 0 < a) {y : Fin (n + 1) → F}
    (hy : ∀ i, 𝒱 (y i) < 1) {k : GL (Fin (n + 2)) F}
    (hk : k ∈ principalLevelSubgroup F (n + 1) a) :
    lowGL (lowerUnip y * k) ∈ principalLevelSubgroup F n a := by
  have hu : lowerUnip y * k ∈ parahoric ϖ :=
    mul_mem (lowerUnip_mem_parahoric hϖ hy) (mem_parahoric_of_principalLevel hϖ ha hk)
  set H := lowGL (lowerUnip y * k) with hH
  have hunit := isUnit_det_low_of_parahoric hϖ hu
  have hHval : H.val = vecMulVec y (rowT k.val) + low k.val := by
    rw [hH, lowGL_val hunit, Units.val_mul, low_mul, colT_lowerUnip, low_lowerUnip,
      Matrix.one_mul]
  have hkent := ((mem_principalLevelSubgroup_iff hϖ k).1 hk).1
  have h1 : ∀ i j, 𝒱 (H.val i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j) ≤
      𝒱 (ϖ : F) ^ a := by
    intro i j
    have e : H.val i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j =
        y i * (k.val 0 j.succ - (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) 0 j.succ) +
          (k.val i.succ j.succ - (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) i.succ j.succ) := by
      rw [hHval, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm, one_succ_succ]
      simp only [Matrix.add_apply, vecMulVec_apply, rowT_apply, low_apply]
      ring
    rw [e]
    apply Valuation.map_add_le
    · rw [map_mul]
      calc 𝒱 (y i) * 𝒱 (k.val 0 j.succ - (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) F) 0 j.succ)
          ≤ 1 * 𝒱 (ϖ : F) ^ a := mul_le_mul' (hy i).le (hkent 0 j.succ)
        _ = 𝒱 (ϖ : F) ^ a := one_mul _
    · exact hkent _ _
  refine (mem_principalLevelSubgroup_iff hϖ H).2 ⟨h1, fun i j => ?_⟩
  have hHK : H ∈ integralSubgroup 𝒪 n := lowGL_mem_integral_of_parahoric hϖ hu
  have e : (H⁻¹).val - 1 = (H⁻¹).val * (1 - H.val) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e' : (H⁻¹).val i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j =
      ((H⁻¹).val * (1 - H.val)) i j := by
    rw [← e]; rfl
  rw [e', Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [map_mul]
  have h2 : 𝒱 ((1 - H.val) l j) ≤ 𝒱 (ϖ : F) ^ a := by
    rw [Matrix.sub_apply, Valuation.map_sub_swap]
    exact h1 l j
  calc 𝒱 ((H⁻¹).val i l) * 𝒱 ((1 - H.val) l j) ≤ 1 * 𝒱 (ϖ : F) ^ a :=
        mul_le_mul' (val_le_one_of_mem (integral_entry (inv_mem hHK) i l)) h2
    _ = 𝒱 (ϖ : F) ^ a := one_mul _

end Langlands.Conductor.SphericalCyclicity
