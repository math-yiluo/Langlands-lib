import Langlands.Representation.Conductor.Congruence

/-!
# Agreement of level-fixed functions off the mirabolic subgroup

Two functions on `GL_(n+1)(F)` that are right invariant under the level-`f` subgroup
`K_1(f)` (last row congruent to the last standard row modulo `𝔭^f`), transform by the
same character under scalar matrices and agree on the mirabolic subgroup, agree at
every matrix whose last row is a nonzero multiple of a row congruent to the last
standard row modulo `𝔭^f`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Matrix

universe uF

variable {F : Type uF} [Field F]


section Membership

variable [ValuativeRel F]

/-- An invertible matrix with integral entries, integral inverse entries and last row
congruent to the last standard row modulo `𝔭^f` lies in the level-`f` subgroup. -/
theorem mem_levelSubgroup_of_entries {n f : ℕ} (g : GeneralLinearGroup (Fin (n + 1)) F)
    (hg : ∀ i j, g i j ∈ (ValuativeRel.valuation F).integer) (hginv : ∀ i j, (g⁻¹ : GeneralLinearGroup (Fin (n + 1)) F) i j ∈ (ValuativeRel.valuation F).integer)
    (hrow : ∀ j, ∃ x : (ValuativeRel.valuation F).integer, x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
      (x : F) = g (Fin.last n) j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j) :
    g ∈ Conductor.levelSubgroup F n f := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ValuativeRel.valuation F).integer := fun i j => ⟨g i j, hg i j⟩
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) (ValuativeRel.valuation F).integer := fun i j =>
    ⟨(g⁻¹ : GeneralLinearGroup (Fin (n + 1)) F) i j, hginv i j⟩
  have hmap : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ValuativeRel.valuation F).integer, M.map ((ValuativeRel.valuation F).integer.subtype) =
      fun i j => ((M i j : (ValuativeRel.valuation F).integer) : F) := fun M => rfl
  have hinj : Function.Injective (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ValuativeRel.valuation F).integer =>
      M.map (ValuativeRel.valuation F).integer.subtype) := by
    intro M N h
    ext i j
    exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := by
    apply hinj
    change (A * B).map (Subring.subtype (ValuativeRel.valuation F).integer) = (1 : Matrix _ _ (ValuativeRel.valuation F).integer).map (Subring.subtype (ValuativeRel.valuation F).integer)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA : A.map (Subring.subtype (ValuativeRel.valuation F).integer) = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := rfl
    have hB : B.map (Subring.subtype (ValuativeRel.valuation F).integer) =
        ((g⁻¹ : GeneralLinearGroup (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := rfl
    rw [hA, hB, ← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one]
  have hBA : B * A = 1 := by
    apply hinj
    change (B * A).map (Subring.subtype (ValuativeRel.valuation F).integer) = (1 : Matrix _ _ (ValuativeRel.valuation F).integer).map (Subring.subtype (ValuativeRel.valuation F).integer)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA : A.map (Subring.subtype (ValuativeRel.valuation F).integer) = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := rfl
    have hB : B.map (Subring.subtype (ValuativeRel.valuation F).integer) =
        ((g⁻¹ : GeneralLinearGroup (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := rfl
    rw [hA, hB, ← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
  let g' : GeneralLinearGroup (Fin (n + 1)) (ValuativeRel.valuation F).integer := ⟨A, B, hAB, hBA⟩
  refine ⟨g', ?_, ?_⟩
  · rw [SetLike.mem_coe, Conductor.mem_integralCongruence]
    intro j
    obtain ⟨x, hx, hxe⟩ := hrow j
    have : g' (Fin.last n) j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (ValuativeRel.valuation F).integer) (Fin.last n) j = x := by
      apply Subtype.ext
      rw [hxe]
      by_cases hj : Fin.last n = j
      · subst hj
        simp [g', A]
      · simp [g', A, Matrix.one_apply_ne hj]
    rw [this]
    exact hx
  · apply Units.ext
    rfl

end Membership

section LastRow

variable {n : ℕ}

/-- The nilpotent matrix with last row `(c_0, …, c_(n-1), 0)`. -/
def lastRowNil (c : Fin (n + 1) → F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  fun i j => if i = Fin.last n ∧ j ≠ Fin.last n then c j else 0

theorem lastRowNil_sq (c : Fin (n + 1) → F) : lastRowNil c * lastRowNil c = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = Fin.last n
  · subst hk
    simp [lastRowNil]
  · simp [lastRowNil, hk]

/-- The lower unipotent matrix `[[I, 0], [c, 1]]`, with inverse `[[I, 0], [-c, 1]]`. -/
def lastRowUnipotent (c : Fin (n + 1) → F) : GeneralLinearGroup (Fin (n + 1)) F where
  val := 1 + lastRowNil c
  inv := 1 - lastRowNil c
  val_inv := by simp [mul_sub, add_mul, lastRowNil_sq]
  inv_val := by simp [sub_mul, mul_add, lastRowNil_sq]

theorem lastRowUnipotent_apply (c : Fin (n + 1) → F) (i j : Fin (n + 1)) :
    lastRowUnipotent c i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j +
      lastRowNil c i j := rfl

theorem lastRowUnipotent_inv_apply (c : Fin (n + 1) → F) (i j : Fin (n + 1)) :
    (lastRowUnipotent c)⁻¹ i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j -
      lastRowNil c i j := rfl

end LastRow

section LevelMembership

variable [ValuativeRel F] {n : ℕ}

/-- Integral coordinates in `𝔭^f` give an element of the level-`f` subgroup. -/
theorem lastRowUnipotent_mem_levelSubgroup {f : ℕ} (c : Fin (n + 1) → F)
    (hc : ∀ j, ∃ x : (ValuativeRel.valuation F).integer, x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧ (x : F) = c j) :
    lastRowUnipotent c ∈ Conductor.levelSubgroup F n f := by
  have hcO : ∀ j, c j ∈ (ValuativeRel.valuation F).integer := fun j => by
    obtain ⟨x, -, hx⟩ := hc j
    rw [← hx]
    exact x.property
  have hone : ∀ i j, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j ∈ (ValuativeRel.valuation F).integer := fun i j => by
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hnil : ∀ i j, lastRowNil c i j ∈ (ValuativeRel.valuation F).integer := fun i j => by
    unfold lastRowNil
    split_ifs
    · exact hcO j
    · exact Subring.zero_mem _
  apply mem_levelSubgroup_of_entries
  · intro i j
    exact Subring.add_mem _ (hone i j) (hnil i j)
  · intro i j
    exact Subring.sub_mem _ (hone i j) (hnil i j)
  · intro j
    rw [lastRowUnipotent_apply, add_sub_cancel_left]
    by_cases hj : j = Fin.last n
    · subst hj
      exact ⟨0, Submodule.zero_mem _, by simp [lastRowNil]⟩
    · obtain ⟨x, hx, hxe⟩ := hc j
      exact ⟨x, hx, by simp [lastRowNil, hj, hxe]⟩

end LevelMembership


section Agreement

variable [ValuativeRel F] {n : ℕ}

/-- The coordinates `ℓ_j / ℓ_last` of a last row, with last coordinate `0`. -/
def lastRowRatios (ℓ : Fin (n + 1) → F) : Fin (n + 1) → F :=
  fun j => if j = Fin.last n then 0 else ℓ j / ℓ (Fin.last n)

omit [ValuativeRel F] in
theorem mul_lastRowUnipotent_inv_lastRow (m : GeneralLinearGroup (Fin (n + 1)) F)
    (hr : m (Fin.last n) (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    ((m : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
        ((lastRowUnipotent (lastRowRatios (m (Fin.last n))))⁻¹ :
          GeneralLinearGroup (Fin (n + 1)) F)) (Fin.last n) j =
      if j = Fin.last n then m (Fin.last n) (Fin.last n) else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [lastRowUnipotent_inv_apply, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ l, m (Fin.last n) l * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) l j =
      m (Fin.last n) j := by
    have := congrFun (congrFun (Matrix.mul_one (m : Matrix (Fin (n + 1)) (Fin (n + 1)) F))
      (Fin.last n)) j
    rwa [Matrix.mul_apply] at this
  have h2 : ∑ l, m (Fin.last n) l * lastRowNil (lastRowRatios (m (Fin.last n))) l j =
      m (Fin.last n) (Fin.last n) * lastRowNil (lastRowRatios (m (Fin.last n))) (Fin.last n) j := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · intro l _ hl
      simp [lastRowNil, hl]
    · simp
  rw [h1, h2]
  by_cases hj : j = Fin.last n
  · subst hj
    simp [lastRowNil]
  · simp only [lastRowNil, lastRowRatios, hj, ite_false, true_and, ne_eq, not_false_eq_true,
      ite_true]
    field_simp
    ring

omit [ValuativeRel F] in
/-- Right multiplication by `[[I,0],[-ℓ/ℓ_last,1]]` and the scalar `ℓ_last⁻¹` brings the
last row `ℓ` to the last standard row. -/
theorem lastRow_mul_lastRowUnipotent_inv (m : GeneralLinearGroup (Fin (n + 1)) F)
    (hr : m (Fin.last n) (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    (m * (lastRowUnipotent (lastRowRatios (m (Fin.last n))))⁻¹ *
        (GeneralLinearGroup.scalar (Fin (n + 1)) (Units.mk0 _ hr))⁻¹) (Fin.last n) j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j := by
  rw [← map_inv, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal,
    mul_lastRowUnipotent_inv_lastRow m hr j]
  by_cases hj : j = Fin.last n
  · subst hj
    simp [hr]
  · simp [hj, Matrix.one_apply_ne (Ne.symm hj)]

/-- Two functions on `GL_(n+1)(F)` that are right invariant under the level-`f` subgroup,
transform by one character `ω` under scalar matrices and agree on the mirabolic subgroup
agree at every matrix whose last row `ℓ` has `ℓ_last ≠ 0` and `ℓ_j / ℓ_last ∈ 𝔭^f`
for `j ≠ last`. -/
theorem eq_of_lastRow_congruence {f : ℕ} (ω : Fˣ →* ℂˣ)
    (W₁ W₂ : GeneralLinearGroup (Fin (n + 1)) F → ℂ)
    (hK₁ : ∀ g k, k ∈ Conductor.levelSubgroup F n f → W₁ (g * k) = W₁ g)
    (hK₂ : ∀ g k, k ∈ Conductor.levelSubgroup F n f → W₂ (g * k) = W₂ g)
    (hZ₁ : ∀ (z : Fˣ) g, W₁ (GeneralLinearGroup.scalar (Fin (n + 1)) z * g) = ω z * W₁ g)
    (hZ₂ : ∀ (z : Fˣ) g, W₂ (GeneralLinearGroup.scalar (Fin (n + 1)) z * g) = ω z * W₂ g)
    (hP : ∀ p : GeneralLinearGroup (Fin (n + 1)) F,
      (∀ j, p (Fin.last n) j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j) →
        W₁ p = W₂ p)
    (m : GeneralLinearGroup (Fin (n + 1)) F) (hr : m (Fin.last n) (Fin.last n) ≠ 0)
    (hc : ∀ j, j ≠ Fin.last n → ∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ f ∧
        (x : F) = m (Fin.last n) j / m (Fin.last n) (Fin.last n)) :
    W₁ m = W₂ m := by
  set k := lastRowUnipotent (lastRowRatios (m (Fin.last n))) with hk
  set z : Fˣ := Units.mk0 _ hr with hz
  set p := m * k⁻¹ * (GeneralLinearGroup.scalar (Fin (n + 1)) z)⁻¹ with hp
  have hkmem : k ∈ Conductor.levelSubgroup F n f := by
    apply lastRowUnipotent_mem_levelSubgroup
    intro j
    by_cases hj : j = Fin.last n
    · subst hj
      exact ⟨0, Submodule.zero_mem _, by simp [lastRowRatios]⟩
    · obtain ⟨x, hx, hxe⟩ := hc j hj
      exact ⟨x, hx, by simp [lastRowRatios, hj, hxe]⟩
  have hm : m = GeneralLinearGroup.scalar (Fin (n + 1)) z * p * k := by
    rw [hp, GeneralLinearGroup.scalar_commute]
    group
  have hpP : ∀ j, p (Fin.last n) j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j :=
    lastRow_mul_lastRowUnipotent_inv m hr
  rw [hm, hK₁ _ _ hkmem, hK₂ _ _ hkmem, hZ₁, hZ₂, hP p hpP]

end Agreement

end Langlands.RankinSelberg.HighlyRamified
