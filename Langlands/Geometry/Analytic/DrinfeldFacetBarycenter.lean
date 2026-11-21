import Langlands.Geometry.Analytic.DrinfeldNearestVertex

/-! # Barycenters of facets of the building of `PGL(V)` over a local field -/

noncomputable section

universe v w

namespace Langlands.Analytic

open Set
open scoped ENNReal

namespace VectorNorm

variable {F : Type v} [NontriviallyNormedField F] {ϖ : F}
  {V : Type w} [AddCommGroup V] [Module F V]

/-- Lattice norms `μ 0 ≤ ⋯ ≤ μ (m - 1)`, all within the factor `q = ‖ϖ‖⁻¹` of each other. -/
structure IsChainData (ϖ : F) {m : ℕ} (μ : Fin m → VectorNorm F V) : Prop where
  isLatticeNorm : ∀ i, (μ i).IsLatticeNorm
  mono : ∀ i j, i ≤ j → ∀ a, μ i a ≤ μ j a
  le_mul : ∀ i j a, μ i a ≤ ‖ϖ‖⁻¹ * μ j a

/-- Distinct values of lattice norms differ at least by the factor `q`. -/
theorem IsLatticeNorm.inv_mul_le_of_lt (hϖ : IsMaxBelowOne ϖ) {ρ ρ' : VectorNorm F V}
    (hρ : ρ.IsLatticeNorm) (hρ' : ρ'.IsLatticeNorm) {a b : V} (hb : b ≠ 0) (h : ρ a < ρ' b) :
    ‖ϖ‖⁻¹ * ρ a ≤ ρ' b := by
  obtain ⟨s, hs⟩ := hρ a
  obtain ⟨t, ht⟩ := hρ' b
  have htpos : 0 < ‖t‖ := ht ▸ ρ'.pos hb
  rw [hs, ht] at h ⊢
  have h1 : ‖s / t‖ < 1 := by
    rw [norm_div, div_lt_one htpos]
    exact h
  have h2 := hϖ.2.2 _ h1
  rw [norm_div, div_le_iff₀ htpos] at h2
  rw [inv_mul_le_iff₀ hϖ.1]
  exact h2

/-- The values of the norms of a chain at two vectors are comparable. -/
theorem IsChainData.comparable (hϖ : IsMaxBelowOne ϖ) {m : ℕ} {μ : Fin m → VectorNorm F V}
    (hμ : IsChainData ϖ μ) (a b : V) : (∀ i, μ i a ≤ μ i b) ∨ (∀ i, μ i b ≤ μ i a) := by
  by_cases h : ∃ i, μ i a < μ i b
  · obtain ⟨i, hi⟩ := h
    have hb : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hi
      exact absurd hi (not_lt.2 ((μ i).nonneg a))
    have hQ := IsLatticeNorm.inv_mul_le_of_lt hϖ (hμ.isLatticeNorm i) (hμ.isLatticeNorm i) hb hi
    left
    intro j
    rcases le_total i j with hij | hji
    · exact (hμ.le_mul j i a).trans (hQ.trans (hμ.mono i j hij b))
    · have h2 : ‖ϖ‖⁻¹ * μ i a ≤ ‖ϖ‖⁻¹ * μ j b := hQ.trans (hμ.le_mul i j b)
      have h3 := le_of_mul_le_mul_left h2 (inv_pos.2 hϖ.1)
      exact (hμ.mono j i hji a).trans h3
  · push Not at h
    exact Or.inr h

/-- The barycenter `a ↦ (∏ᵢ μ i a) ^ (1 / m)` of a chain of lattice norms. -/
def barycenter (hϖ : IsMaxBelowOne ϖ) {m : ℕ} (hm : 0 < m) (μ : Fin m → VectorNorm F V)
    (hμ : IsChainData ϖ μ) : VectorNorm F V where
  toFun a := (∏ i, μ i a) ^ ((m : ℝ)⁻¹)
  pos' a ha := Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => (μ i).pos ha) _
  smul' t a := by
    simp only [VectorNorm.map_smul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [Real.mul_rpow (pow_nonneg (norm_nonneg t) m)
      (Finset.prod_nonneg fun i _ => (μ i).nonneg a),
      Real.pow_rpow_inv_natCast (norm_nonneg t) hm.ne']
  add_le_max' a b := by
    rcases hμ.comparable hϖ a b with h | h
    · refine le_max_of_le_right (Real.rpow_le_rpow
        (Finset.prod_nonneg fun i _ => (μ i).nonneg _) ?_ (by positivity))
      exact Finset.prod_le_prod₀ (fun i _ => (μ i).nonneg _)
        fun i _ => ((μ i).add_le_max a b).trans (max_le (h i) le_rfl)
    · refine le_max_of_le_left (Real.rpow_le_rpow
        (Finset.prod_nonneg fun i _ => (μ i).nonneg _) ?_ (by positivity))
      exact Finset.prod_le_prod₀ (fun i _ => (μ i).nonneg _)
        fun i _ => ((μ i).add_le_max a b).trans (max_le le_rfl (h i))

/-- The constant `q ^ ((m - 1) / m)`. -/
def baryConst (ϖ : F) (m : ℕ) : ℝ := (‖ϖ‖⁻¹ ^ (m - 1)) ^ ((m : ℝ)⁻¹)

private theorem int_eq_of_mul_sub_eq {m j j' x y : ℤ} (hj : 0 ≤ j) (hj' : j < m) (hjj : 0 ≤ j')
    (hjj' : j' < m) (h : m * x - j = m * y - j') : j = j' := by
  have hd : m * (x - y) = j - j' := by rw [mul_sub]; linarith
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have : m * (x - y) ≤ -m := by nlinarith
    linarith
  · subst hxy
    linarith
  · have : m ≤ m * (x - y) := by nlinarith
    linarith

section Bounds

variable (hϖ : IsMaxBelowOne ϖ) {m : ℕ} (hm : 0 < m) {μ : Fin m → VectorNorm F V}
  (hμ : IsChainData ϖ μ)
include hϖ hμ

theorem barycenter_apply (a : V) :
    barycenter hϖ hm μ hμ a = (∏ i, μ i a) ^ ((m : ℝ)⁻¹) := rfl

theorem barycenter_pow (a : V) : barycenter hϖ hm μ hμ a ^ m = ∏ i, μ i a :=
  Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => (μ i).nonneg a) hm.ne'

/-- The barycenter is at distance at most `q ^ ((m - 1) / m)` from each norm of the chain. -/
theorem distRatio_barycenter_le (j : Fin m) :
    distRatio (barycenter hϖ hm μ hμ) (μ j) ≤ ENNReal.ofReal (baryConst ϖ m) := by
  classical
  have hQ : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  set c : Fin m → ℝ := fun i => if j < i then ‖ϖ‖⁻¹ else 1 with hc
  set d : Fin m → ℝ := fun i => if i < j then ‖ϖ‖⁻¹ else 1 with hd
  have hc0 : ∀ i, 0 ≤ c i := fun i => by
    simp only [hc]
    split_ifs <;> positivity
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    simp only [hd]
    split_ifs <;> positivity
  have hC0 : 0 ≤ ∏ i, c i := Finset.prod_nonneg fun i _ => hc0 i
  have hD0 : 0 ≤ ∏ i, d i := Finset.prod_nonneg fun i _ => hd0 i
  have hCD : (∏ i, c i) * ∏ i, d i = ‖ϖ‖⁻¹ ^ (m - 1) := by
    rw [← Finset.prod_mul_distrib]
    have hcd : ∀ i, c i * d i = if i = j then 1 else ‖ϖ‖⁻¹ := by
      intro i
      simp only [hc, hd]
      rcases lt_trichotomy i j with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · simp [h]
      · simp [h, h.ne', not_lt.2 h.le]
    simp only [hcd]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have h1 : ∀ a, barycenter hϖ hm μ hμ a ≤ (∏ i, c i) ^ ((m : ℝ)⁻¹) * μ j a := by
    intro a
    have hle : ∏ i, μ i a ≤ ∏ i, (c i * μ j a) :=
      Finset.prod_le_prod₀ (fun i _ => (μ i).nonneg a) fun i _ => by
        simp only [hc]
        split_ifs with h
        · exact hμ.le_mul i j a
        · rw [one_mul]
          exact hμ.mono i j (not_lt.1 h) a
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
    rw [barycenter_apply]
    calc (∏ i, μ i a) ^ ((m : ℝ)⁻¹) ≤ ((∏ i, c i) * μ j a ^ m) ^ ((m : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => (μ i).nonneg a) hle (by positivity)
      _ = (∏ i, c i) ^ ((m : ℝ)⁻¹) * μ j a := by
          rw [Real.mul_rpow hC0 (pow_nonneg ((μ j).nonneg a) m),
            Real.pow_rpow_inv_natCast ((μ j).nonneg a) hm.ne']
  have h2 : ∀ a, μ j a ≤ (∏ i, d i) ^ ((m : ℝ)⁻¹) * barycenter hϖ hm μ hμ a := by
    intro a
    have hle : ∏ _i : Fin m, μ j a ≤ ∏ i, (d i * μ i a) :=
      Finset.prod_le_prod₀ (fun _ _ => (μ j).nonneg a) fun i _ => by
        simp only [hd]
        split_ifs with h
        · exact hμ.le_mul j i a
        · rw [one_mul]
          exact hμ.mono j i (not_lt.1 h) a
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
    rw [barycenter_apply, ← Real.mul_rpow hD0 (Finset.prod_nonneg fun i _ => (μ i).nonneg a)]
    calc μ j a = (μ j a ^ m) ^ ((m : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast ((μ j).nonneg a) hm.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (pow_nonneg ((μ j).nonneg a) m) hle (by positivity)
  have hr1 : ratioSup (barycenter hϖ hm μ hμ) (μ j) ≤
      ENNReal.ofReal ((∏ i, c i) ^ ((m : ℝ)⁻¹)) :=
    ratioSup_le_ofReal (Real.rpow_nonneg hC0 _) fun a _ => h1 a
  have hr2 : ratioSup (μ j) (barycenter hϖ hm μ hμ) ≤
      ENNReal.ofReal ((∏ i, d i) ^ ((m : ℝ)⁻¹)) :=
    ratioSup_le_ofReal (Real.rpow_nonneg hD0 _) fun a _ => h2 a
  calc distRatio (barycenter hϖ hm μ hμ) (μ j)
      ≤ ENNReal.ofReal ((∏ i, c i) ^ ((m : ℝ)⁻¹)) *
          ENNReal.ofReal ((∏ i, d i) ^ ((m : ℝ)⁻¹)) := mul_le_mul' hr1 hr2
    _ = ENNReal.ofReal (baryConst ϖ m) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC0 _), ← Real.mul_rpow hC0 hD0, hCD,
          baryConst]

/-- In a chain with pairwise distinct classes, for every `j` there is `b ≠ 0` on which
all values equal `μ 0 b` if `j = 0`; otherwise they jump from `μ 0 b` to `q μ 0 b` at `j`. -/
theorem IsChainData.exists_pattern [Nontrivial V]
    (hinj : Function.Injective fun i => (⟦μ i⟧ : NormClass F V)) (j : Fin m) :
    ∃ b : V, b ≠ 0 ∧ ∀ i, μ i b = (if 0 < (j : ℕ) ∧ j ≤ i then ‖ϖ‖⁻¹ else 1) * μ ⟨0, hm⟩ b := by
  have hQ : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  set z : Fin m := ⟨0, hm⟩ with hz
  have hzle : ∀ i, z ≤ i := fun i => Fin.mk_le_of_le_val (Nat.zero_le _)
  have hlat := hμ.isLatticeNorm
  by_cases hj : (j : ℕ) = 0
  · -- a vector on which the whole chain is constant
    have key : ∃ b : V, b ≠ 0 ∧ ∀ i, μ i b = μ z b := by
      by_cases hm1 : m = 1
      · obtain ⟨b, hb⟩ := exists_ne (0 : V)
        refine ⟨b, hb, fun i => ?_⟩
        have : i = z := Fin.ext (by have := i.2; simp [hz]; omega)
        rw [this]
      · set l : Fin m := ⟨m - 1, by omega⟩ with hl
        have hlz : l ≠ z := by
          intro h
          have := congrArg Fin.val h
          simp [hl, hz] at this
          omega
        have hne : ∃ b, μ l b ≠ ‖ϖ‖⁻¹ * μ z b := by
          by_contra hall
          push Not at hall
          have hh : Homothetic (μ z) (μ l) := ⟨‖ϖ‖⁻¹, hQ, hall⟩
          exact hlz (hinj (Quotient.sound hh).symm)
        obtain ⟨b, hb⟩ := hne
        have hb0 : b ≠ 0 := by
          rintro rfl
          simp at hb
        have hlt : μ l b < ‖ϖ‖⁻¹ * μ z b := lt_of_le_of_ne (hμ.le_mul l z b) hb
        have hlzb : μ l b = μ z b := by
          refine le_antisymm ?_ (hμ.mono z l (hzle l) b)
          by_contra hgt
          push Not at hgt
          have := IsLatticeNorm.inv_mul_le_of_lt hϖ (hlat z) (hlat l) hb0 hgt
          linarith
        refine ⟨b, hb0, fun i => le_antisymm ?_ (hμ.mono z i (hzle i) b)⟩
        rw [← hlzb]
        exact hμ.mono i l (Fin.mk_le_of_le_val (by have := i.2; simp [hl]; omega)) b
    obtain ⟨b, hb0, hb⟩ := key
    refine ⟨b, hb0, fun i => ?_⟩
    rw [ite_eq_right (by omega), one_mul]
    exact hb i
  · set j' : Fin m := ⟨(j : ℕ) - 1, by omega⟩ with hj'
    have hj'j : j' < j := Fin.mk_lt_of_lt_val (by omega)
    have hne : ∃ b, μ j' b ≠ μ j b := by
      by_contra hall
      push Not at hall
      exact hj'j.ne (hinj (congrArg _ (VectorNorm.ext hall)))
    obtain ⟨b, hb⟩ := hne
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    have hlt : μ j' b < μ j b := lt_of_le_of_ne (hμ.mono j' j hj'j.le b) hb
    have hjump := IsLatticeNorm.inv_mul_le_of_lt hϖ (hlat j') (hlat j) hb0 hlt
    have hj'z : μ j' b = μ z b := by
      refine le_antisymm ?_ (hμ.mono z j' (hzle j') b)
      by_contra hgt
      push Not at hgt
      have h1 := IsLatticeNorm.inv_mul_le_of_lt hϖ (hlat z) (hlat j') hb0 hgt
      have h2 := hμ.le_mul j z b
      linarith
    have hjz : μ j b = ‖ϖ‖⁻¹ * μ z b := by
      refine le_antisymm (hμ.le_mul j z b) ?_
      rw [← hj'z]
      exact hjump
    refine ⟨b, hb0, fun i => ?_⟩
    by_cases hji : j ≤ i
    · rw [ite_eq_left ⟨by omega, hji⟩]
      exact le_antisymm (hμ.le_mul i z b) (hjz ▸ hμ.mono j i hji b)
    · rw [ite_eq_right (fun h => hji h.2), one_mul]
      push Not at hji
      have hij' : i ≤ j' := Fin.mk_le_of_le_val (by
        have : (i : ℕ) < j := hji
        simp [hj']
        omega)
      exact le_antisymm (hj'z ▸ hμ.mono i j' hij' b) (hμ.mono z i (hzle i) b)

/-- The barycenter of a chain with pairwise distinct classes is at distance at least
`q ^ ((m - 1) / m)` from every lattice norm. -/
theorem le_distRatio_barycenter [Nontrivial V]
    (hinj : Function.Injective fun i => (⟦μ i⟧ : NormClass F V)) {μ' : VectorNorm F V}
    (hμ' : μ'.IsLatticeNorm) :
    ENNReal.ofReal (baryConst ϖ m) ≤ distRatio (barycenter hϖ hm μ hμ) μ' := by
  classical
  have hQ : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  have hQ1 := hϖ.one_lt_inv
  set ν := barycenter hϖ hm μ hμ with hν
  set z : Fin m := ⟨0, hm⟩ with hz
  choose b hb0 hb using IsChainData.exists_pattern hϖ hm hμ hinj
  have hK : ∀ j : Fin m, ∃ n : ℤ,
      (ν (b j) / μ' (b j)) ^ m = ‖ϖ‖⁻¹ ^ ((m : ℤ) * n - ((j : ℕ) : ℤ)) := by
    intro j
    obtain ⟨s, hs⟩ := hμ.isLatticeNorm z (b j)
    obtain ⟨t, ht⟩ := hμ' (b j)
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hs
      exact ((μ z).pos (hb0 j)).ne' hs
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [norm_zero] at ht
      exact (μ'.pos (hb0 j)).ne' ht
    obtain ⟨x, hx⟩ := hϖ.exists_norm_eq_zpow hs0
    obtain ⟨y, hy⟩ := hϖ.exists_norm_eq_zpow ht0
    set c := (Finset.univ.filter fun i : Fin m => 0 < (j : ℕ) ∧ j ≤ i).card with hc
    obtain ⟨e, he⟩ : ∃ e : ℤ, (c : ℤ) = m * e - ((j : ℕ) : ℤ) := by
      by_cases hj : (j : ℕ) = 0
      · refine ⟨0, ?_⟩
        have : (Finset.univ.filter fun i : Fin m => 0 < (j : ℕ) ∧ j ≤ i) = ∅ := by
          ext i
          simp [hj]
        rw [hc, this, Finset.card_empty, hj]
        ring
      · refine ⟨1, ?_⟩
        have : (Finset.univ.filter fun i : Fin m => 0 < (j : ℕ) ∧ j ≤ i) = Finset.Ici j := by
          ext i
          simp [Nat.pos_of_ne_zero hj]
        rw [hc, this, Fin.card_Ici]
        have := j.2
        rw [Nat.cast_sub this.le]
        ring
    refine ⟨e + x - y, ?_⟩
    have hprod : ν (b j) ^ m = ‖ϖ‖⁻¹ ^ c * μ z (b j) ^ m := by
      rw [hν, barycenter_pow, Finset.prod_congr rfl (fun i _ => hb j i),
        Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [div_pow, hprod, hs, hx, ht, hy, ← zpow_natCast, ← zpow_natCast (‖ϖ‖⁻¹ ^ x),
      ← zpow_natCast (‖ϖ‖⁻¹ ^ y), ← zpow_mul, ← zpow_mul, ← zpow_add₀ hQ.ne',
      ← zpow_sub₀ hQ.ne', he]
    congr 1
    ring
  choose n hn using hK
  set K : Fin m → ℤ := fun j => (m : ℤ) * n j - ((j : ℕ) : ℤ) with hKdef
  have hKinj : Function.Injective K := by
    intro j j' h
    have := int_eq_of_mul_sub_eq (m := (m : ℤ)) (j := ((j : ℕ) : ℤ)) (j' := ((j' : ℕ) : ℤ))
      (x := n j) (y := n j') (Int.natCast_nonneg _) (by exact_mod_cast j.2)
      (Int.natCast_nonneg _) (by exact_mod_cast j'.2) h
    exact Fin.ext (by exact_mod_cast this)
  obtain ⟨jM, -, hjM⟩ := Finset.univ.exists_max_image K ⟨z, Finset.mem_univ _⟩
  obtain ⟨jm, -, hjm⟩ := Finset.univ.exists_min_image K ⟨z, Finset.mem_univ _⟩
  have hspread : (m : ℤ) - 1 ≤ K jM - K jm := by
    have hsub : Finset.univ.image K ⊆ Finset.Icc (K jm) (K jM) := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_Icc.2 ⟨hjm j (Finset.mem_univ _), hjM j (Finset.mem_univ _)⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hKinj, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc] at hcard
    omega
  set ρ : Fin m → ℝ := fun j => ν (b j) / μ' (b j) with hρ
  have hρpos : ∀ j, 0 < ρ j := fun j => div_pos (ν.pos (hb0 j)) (μ'.pos (hb0 j))
  set r := ρ jM / ρ jm with hr_def
  have hr : 0 < r := div_pos (hρpos jM) (hρpos jm)
  have hrm : ‖ϖ‖⁻¹ ^ (m - 1) ≤ r ^ m := by
    rw [hr_def, div_pow, hρ]
    simp only
    rw [hn jM, hn jm, ← zpow_sub₀ hQ.ne', ← zpow_natCast]
    apply zpow_le_zpow_right₀ hQ1.le
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    exact hspread
  have hbary : baryConst ϖ m ≤ r := by
    rw [baryConst]
    calc (‖ϖ‖⁻¹ ^ (m - 1)) ^ ((m : ℝ)⁻¹) ≤ (r ^ m) ^ ((m : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hrm (by positivity)
      _ = r := Real.pow_rpow_inv_natCast hr.le hm.ne'
  have hd : ENNReal.ofReal r ≤ distRatio ν μ' := by
    have h1 := le_ratioSup ν μ' (b jM)
    have h2 := le_ratioSup μ' ν (b jm)
    calc ENNReal.ofReal r
        = ENNReal.ofReal (ν (b jM) / μ' (b jM)) * ENNReal.ofReal (μ' (b jm) / ν (b jm)) := by
          rw [← ENNReal.ofReal_mul (hρpos jM).le, hr_def, hρ]
          simp only
          rw [div_eq_mul_inv (ν (b jM) / μ' (b jM)), inv_div]
      _ ≤ distRatio ν μ' := mul_le_mul' h1 h2
  exact (ENNReal.ofReal_le_ofReal hbary).trans hd

end Bounds

/-- A chain of lattices can be shortened to a chain with pairwise distinct classes and the same
set of classes. -/
theorem IsLatticeChain.exists_strict (hϖ : IsMaxBelowOne ϖ) {k : ℕ}
    {ν : Fin (k + 1) → VectorNorm F V} (hν : IsLatticeChain ν) :
    ∃ (m : ℕ) (_hm : 0 < m) (μ : Fin m → VectorNorm F V), IsChainData ϖ μ ∧
      Function.Injective (fun i => (⟦μ i⟧ : NormClass F V)) ∧
      (range fun i => (⟦μ i⟧ : NormClass F V)) = range fun i => (⟦ν i⟧ : NormClass F V) := by
  classical
  set I := Finset.univ.filter
    fun i : Fin (k + 1) => ∀ j < i, (⟦ν j⟧ : NormClass F V) ≠ ⟦ν i⟧ with hI
  have h0 : (0 : Fin (k + 1)) ∈ I := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j hj => ?_⟩
    exact absurd hj (Fin.not_lt_zero j)
  have hle : ∀ i a, ν i a ≤ ‖ϖ‖⁻¹ * ν 0 a := by
    intro i a
    have h1 := hν.bounded ϖ hϖ.2.1 a
    calc ν i a ≤ ν (Fin.last k) a := hν.mono i (Fin.last k) (Fin.le_last i) a
      _ = ‖ϖ‖⁻¹ * (‖ϖ‖ * ν (Fin.last k) a) := by
          rw [← mul_assoc, inv_mul_cancel₀ hϖ.1.ne', one_mul]
      _ ≤ ‖ϖ‖⁻¹ * ν 0 a := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hϖ.1).le
  set g := I.orderEmbOfFin rfl with hg
  refine ⟨I.card, Finset.card_pos.2 ⟨0, h0⟩, fun j => ν (g j),
    ⟨fun j => hν.isLatticeNorm _, fun i j hij a => hν.mono _ _ (g.monotone hij) a,
      fun i j a => (hle (g i) a).trans (mul_le_mul_of_nonneg_left
        (hν.mono 0 (g j) (Fin.zero_le _) a) (inv_pos.2 hϖ.1).le)⟩, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hgj := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem I rfl j)).2
      exact hgj (g i) (g.strictMono h) hij
    · have hgi := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem I rfl i)).2
      exact hgi (g j) (g.strictMono h) hij.symm
  · ext e
    simp only [Set.mem_range]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨g j, rfl⟩
    · rintro ⟨i, rfl⟩
      set J := Finset.univ.filter
        fun i' : Fin (k + 1) => (⟦ν i'⟧ : NormClass F V) = ⟦ν i⟧ with hJ
      have hJne : J.Nonempty := ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
      have hi₀J : J.min' hJne ∈ J := J.min'_mem hJne
      have hi₀ : (⟦ν (J.min' hJne)⟧ : NormClass F V) = ⟦ν i⟧ := (Finset.mem_filter.1 hi₀J).2
      have hi₀I : J.min' hJne ∈ I := by
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j hj heq => ?_⟩
        have hjJ : j ∈ J := Finset.mem_filter.2 ⟨Finset.mem_univ _, heq.trans hi₀⟩
        exact absurd (J.min'_le j hjJ) (not_le.2 hj)
      have hrange : J.min' hJne ∈ Set.range g := by
        rw [hg, Finset.range_orderEmbOfFin]
        exact hi₀I
      obtain ⟨j, hj⟩ := hrange
      exact ⟨j, by rw [hj]; exact hi₀⟩

end VectorNorm

namespace NormClass

variable {F : Type v} [NontriviallyNormedField F] {ϖ : F}
  {V : Type w} [AddCommGroup V] [Module F V]

/-- Every facet of the building has a point (its barycenter) in the stars of all its vertices. -/
theorem exists_mem_vertexStar_of_isFacet (hϖ : VectorNorm.IsMaxBelowOne ϖ) [Nontrivial V]
    {S : Set (NormClass F V)} (hS : IsFacet S) : ∃ x : NormClass F V, ∀ e ∈ S, x ∈ vertexStar e := by
  obtain ⟨k, ν, hν, rfl⟩ := hS
  obtain ⟨m, hm, μ, hμ, hinj, hrange⟩ := VectorNorm.IsLatticeChain.exists_strict hϖ hν
  refine ⟨⟦VectorNorm.barycenter hϖ hm μ hμ⟧, ?_⟩
  rw [← hrange]
  rintro _ ⟨j, rfl⟩ e' ⟨μ', rfl, hμ'⟩
  exact (VectorNorm.distRatio_barycenter_le hϖ hm hμ j).trans
    (VectorNorm.le_distRatio_barycenter hϖ hm hμ hinj hμ')

end NormClass

end Langlands.Analytic
