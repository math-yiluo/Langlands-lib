import Langlands.Group.GL.UpperUnipotentFactorizationStatement
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Constructions

/-!
# Proof of the plus-minus multiplication homeomorphism

The factors of an upper unipotent matrix are produced by iterating an explicit
polynomial step map `n` times; see the paired Markdown.
-/

namespace Langlands.GeneralLinear

universe u

namespace UpperUnipotentFactorization

variable {n : ℕ} {R : Type u} [CommRing R] (w : Equiv.Perm (Fin n))

/-- Keep the strictly upper entries `(i, j)` whose order `w` preserves. -/
def plusPart (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i < j ∧ w i < w j then Z i j else 0

/-- Keep the strictly upper entries `(i, j)` whose order `w` reverses. -/
def minusPart (Z : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i < j ∧ w j < w i then Z i j else 0

/-- One step of the recursion for the strict parts `(N, M)` of the two factors
of `u = (1 + N) * (1 + M)`. -/
def step (u : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R :=
  (plusPart w (u - 1 - X.1 * X.2), minusPart w (u - 1 - X.1 * X.2))

/-- The strict parts of the two factors: `n` steps starting from zero. -/
def strictParts (u : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R :=
  (step w u)^[n] (0, 0)

/-- The plus factor `1 + N`, as a matrix. -/
def plusMatrix (u : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  1 + (strictParts w u).1

/-- The minus factor `1 + M`, as a matrix. -/
def minusMatrix (u : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  1 + (strictParts w u).2

/-- Matrices vanishing on and below the diagonal. -/
def StrictUpper (N : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, ¬ i < j → N i j = 0

/-- Two matrices agree on all entries `(i, j)` with `j < i + m`. -/
def AgreeBelow (m : ℕ) (N N' : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, j.val < i.val + m → N i j = N' i j

variable {w}

theorem strictUpper_plusPart (Z : Matrix (Fin n) (Fin n) R) :
    StrictUpper (plusPart w Z) := by
  intro i j h
  simp [plusPart, h]

theorem strictUpper_minusPart (Z : Matrix (Fin n) (Fin n) R) :
    StrictUpper (minusPart w Z) := by
  intro i j h
  simp [minusPart, h]

theorem mul_apply_eq_zero {N M : Matrix (Fin n) (Fin n) R}
    (hN : StrictUpper N) (hM : StrictUpper M) {i j : Fin n} (h : ¬ i < j) :
    (N * M) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · have hkj : ¬ k < j := fun hkj => h (hik.trans hkj)
    rw [hM k j hkj, mul_zero]
  · rw [hN i k hik, zero_mul]

theorem agreeBelow_mul {m : ℕ} {N M N' M' : Matrix (Fin n) (Fin n) R}
    (hN : StrictUpper N) (hM : StrictUpper M) (hN' : StrictUpper N')
    (hM' : StrictUpper M') (h₁ : AgreeBelow m N N') (h₂ : AgreeBelow m M M') :
    AgreeBelow (m + 1) (N * M) (N' * M') := by
  intro i j hij
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i < k
  · by_cases hkj : k < j
    · have hik' : i.val < k.val := hik
      have hkj' : k.val < j.val := hkj
      rw [h₁ i k (by omega), h₂ k j (by omega)]
    · rw [hM k j hkj, hM' k j hkj, mul_zero, mul_zero]
  · rw [hN i k hik, hN' i k hik, zero_mul, zero_mul]

theorem agreeBelow_plusPart {m : ℕ} {Z Z' : Matrix (Fin n) (Fin n) R}
    (h : AgreeBelow m Z Z') : AgreeBelow m (plusPart w Z) (plusPart w Z') := by
  intro i j hij
  simp only [plusPart, Matrix.of_apply, h i j hij]

theorem agreeBelow_minusPart {m : ℕ} {Z Z' : Matrix (Fin n) (Fin n) R}
    (h : AgreeBelow m Z Z') : AgreeBelow m (minusPart w Z) (minusPart w Z') := by
  intro i j hij
  simp only [minusPart, Matrix.of_apply, h i j hij]

theorem agreeBelow_sub {m : ℕ} (u : Matrix (Fin n) (Fin n) R)
    {Z Z' : Matrix (Fin n) (Fin n) R} (h : AgreeBelow m Z Z') :
    AgreeBelow m (u - 1 - Z) (u - 1 - Z') := by
  intro i j hij
  simp only [Matrix.sub_apply, h i j hij]

theorem strictUpper_step (u : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R) :
    StrictUpper (step w u X).1 ∧ StrictUpper (step w u X).2 :=
  ⟨strictUpper_plusPart _, strictUpper_minusPart _⟩

theorem strictUpper_iterate (u : Matrix (Fin n) (Fin n) R)
    {X : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R}
    (hX : StrictUpper X.1 ∧ StrictUpper X.2) (m : ℕ) :
    StrictUpper ((step w u)^[m] X).1 ∧ StrictUpper ((step w u)^[m] X).2 := by
  cases m with
  | zero => exact hX
  | succ m =>
    rw [Function.iterate_succ_apply']
    exact strictUpper_step u _

theorem agreeBelow_step (u : Matrix (Fin n) (Fin n) R) {m : ℕ}
    {X Y : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R}
    (hX : StrictUpper X.1 ∧ StrictUpper X.2) (hY : StrictUpper Y.1 ∧ StrictUpper Y.2)
    (h₁ : AgreeBelow m X.1 Y.1) (h₂ : AgreeBelow m X.2 Y.2) :
    AgreeBelow (m + 1) (step w u X).1 (step w u Y).1 ∧
      AgreeBelow (m + 1) (step w u X).2 (step w u Y).2 := by
  have h := agreeBelow_sub u (agreeBelow_mul hX.1 hX.2 hY.1 hY.2 h₁ h₂)
  exact ⟨agreeBelow_plusPart h, agreeBelow_minusPart h⟩

/-- After `m` steps, any two strictly upper starting pairs agree below gap `m`. -/
theorem agreeBelow_iterate (u : Matrix (Fin n) (Fin n) R)
    {X Y : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R}
    (hX : StrictUpper X.1 ∧ StrictUpper X.2) (hY : StrictUpper Y.1 ∧ StrictUpper Y.2)
    (m : ℕ) :
    AgreeBelow m ((step w u)^[m] X).1 ((step w u)^[m] Y).1 ∧
      AgreeBelow m ((step w u)^[m] X).2 ((step w u)^[m] Y).2 := by
  induction m with
  | zero =>
    simp only [Function.iterate_zero_apply]
    constructor <;> intro i j hij <;>
      have h : ¬ i < j := fun h' => by
        have : i.val < j.val := h'
        omega
    · rw [hX.1 i j h, hY.1 i j h]
    · rw [hX.2 i j h, hY.2 i j h]
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact agreeBelow_step u (strictUpper_iterate u hX m) (strictUpper_iterate u hY m)
      ih.1 ih.2

omit [CommRing R] in
theorem eq_of_agreeBelow {N N' : Matrix (Fin n) (Fin n) R} (h : AgreeBelow n N N') :
    N = N' :=
  Matrix.ext fun i j => h i j (by have := j.isLt; omega)

/-- The strict parts are a fixed point of the step map, for every matrix `u`. -/
theorem step_strictParts (u : Matrix (Fin n) (Fin n) R) :
    step w u (strictParts w u) = strictParts w u := by
  have h0 : StrictUpper ((0, 0) : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R).1 ∧
      StrictUpper ((0, 0) : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R).2 :=
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  have h := agreeBelow_iterate (w := w) u (strictUpper_step (w := w) u (0, 0)) h0 n
  unfold strictParts
  rw [← Function.iterate_succ_apply' (step w u) n (0, 0), Function.iterate_succ_apply]
  exact Prod.ext (eq_of_agreeBelow h.1) (eq_of_agreeBelow h.2)

theorem strictParts_fst_apply (u : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (strictParts w u).1 i j =
      if i < j ∧ w i < w j then
        (u - 1 - (strictParts w u).1 * (strictParts w u).2) i j
      else 0 :=
  (congrArg (fun X => X.1 i j) (step_strictParts (w := w) u)).symm

theorem strictParts_snd_apply (u : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (strictParts w u).2 i j =
      if i < j ∧ w j < w i then
        (u - 1 - (strictParts w u).1 * (strictParts w u).2) i j
      else 0 :=
  (congrArg (fun X => X.2 i j) (step_strictParts (w := w) u)).symm

theorem strictUpper_strictParts (u : Matrix (Fin n) (Fin n) R) :
    StrictUpper (strictParts w u).1 ∧ StrictUpper (strictParts w u).2 := by
  rw [← step_strictParts]
  exact strictUpper_step u _

/-- For an upper unipotent `u`, the two factors multiply back to `u`. -/
theorem plusMatrix_mul_minusMatrix_of {u : Matrix (Fin n) (Fin n) R}
    (hu₁ : ∀ i j : Fin n, j < i → u i j = 0) (hu₂ : ∀ i : Fin n, u i i = 1) :
    plusMatrix w u * minusMatrix w u = u := by
  obtain ⟨hN, hM⟩ := strictUpper_strictParts (w := w) u
  have hsum : (strictParts w u).1 + (strictParts w u).2 =
      u - 1 - (strictParts w u).1 * (strictParts w u).2 := by
    ext i j
    rw [Matrix.add_apply, strictParts_fst_apply, strictParts_snd_apply]
    by_cases hij : i < j
    · have hne : w i ≠ w j := w.injective.ne hij.ne
      rcases lt_or_gt_of_ne hne with h | h
      · simp [hij, h, not_lt_of_gt h]
      · simp [hij, h, not_lt_of_gt h]
    · simp only [hij, false_and, ite_false, add_zero]
      rw [Matrix.sub_apply, Matrix.sub_apply, mul_apply_eq_zero hN hM hij]
      rcases eq_or_lt_of_le (not_lt.mp hij) with h | h
      · subst h
        simp [hu₂]
      · simp [hu₁ i j h, Matrix.one_apply_ne h.ne']
  unfold plusMatrix minusMatrix
  calc (1 + (strictParts w u).1) * (1 + (strictParts w u).2)
      = 1 + ((strictParts w u).1 + (strictParts w u).2) +
          (strictParts w u).1 * (strictParts w u).2 := by noncomm_ring
    _ = u := by rw [hsum]; abel

theorem plusMatrix_apply_self (u : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    plusMatrix w u i i = 1 := by
  rw [plusMatrix, Matrix.add_apply, strictParts_fst_apply]
  simp

theorem minusMatrix_apply_self (u : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    minusMatrix w u i i = 1 := by
  rw [minusMatrix, Matrix.add_apply, strictParts_snd_apply]
  simp

theorem plusMatrix_apply_eq_zero (u : Matrix (Fin n) (Fin n) R) {i j : Fin n}
    (hne : i ≠ j) (h : ¬ (i < j ∧ w i < w j)) : plusMatrix w u i j = 0 := by
  rw [plusMatrix, Matrix.add_apply, strictParts_fst_apply, ite_eq_right h,
    Matrix.one_apply_ne hne, add_zero]

theorem minusMatrix_apply_eq_zero (u : Matrix (Fin n) (Fin n) R) {i j : Fin n}
    (hne : i ≠ j) (h : ¬ (i < j ∧ w j < w i)) : minusMatrix w u i j = 0 := by
  rw [minusMatrix, Matrix.add_apply, strictParts_snd_apply, ite_eq_right h,
    Matrix.one_apply_ne hne, add_zero]

theorem plusMatrix_mul_minusMatrix (g : upperUnipotent n R) :
    plusMatrix w g.val.val * minusMatrix w g.val.val = g.val.val :=
  plusMatrix_mul_minusMatrix_of (fun _ _ h => g.property.1 h) g.property.2

variable (w)

/-- The plus factor as an invertible matrix, with inverse `minus * g⁻¹`. -/
def plusUnit (g : upperUnipotent n R) : Langlands.GeneralLinear n R where
  val := plusMatrix w g.val.val
  inv := minusMatrix w g.val.val * (g.val⁻¹ : Langlands.GeneralLinear n R).val
  val_inv := by
    rw [← Matrix.mul_assoc, plusMatrix_mul_minusMatrix, Units.mul_inv]
  inv_val := mul_eq_one_comm.mp (by
    rw [← Matrix.mul_assoc, plusMatrix_mul_minusMatrix, Units.mul_inv])

theorem inv_mul_plusMatrix_mul_minusMatrix (g : upperUnipotent n R) :
    (g.val⁻¹ : Langlands.GeneralLinear n R).val * plusMatrix w g.val.val *
      minusMatrix w g.val.val = 1 := by
  rw [Matrix.mul_assoc, plusMatrix_mul_minusMatrix, Units.inv_mul]

/-- The minus factor as an invertible matrix, with inverse `g⁻¹ * plus`. -/
def minusUnit (g : upperUnipotent n R) : Langlands.GeneralLinear n R where
  val := minusMatrix w g.val.val
  inv := (g.val⁻¹ : Langlands.GeneralLinear n R).val * plusMatrix w g.val.val
  val_inv := mul_eq_one_comm.mp (inv_mul_plusMatrix_mul_minusMatrix w g)
  inv_val := inv_mul_plusMatrix_mul_minusMatrix w g

theorem plusUnit_mem (g : upperUnipotent n R) :
    plusUnit w g ∈ permutationUnipotentPlus n R w := by
  rw [mem_permutationUnipotentPlus_iff_entries, mem_upperUnipotent_iff]
  refine ⟨⟨fun i j hji => ?_, fun i => plusMatrix_apply_self _ i⟩, fun i j hji => ?_⟩
  · exact plusMatrix_apply_eq_zero _ hji.ne' (fun h => (lt_asymm hji) h.1)
  · have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hji
    exact plusMatrix_apply_eq_zero _ hne (fun h => (lt_asymm hji) h.2)

theorem minusUnit_mem (g : upperUnipotent n R) :
    minusUnit w g ∈ permutationUnipotentMinus n R w := by
  rw [mem_permutationUnipotentMinus_iff_entries, mem_upperUnipotent_iff]
  refine ⟨⟨fun i j hji => ?_, fun i => minusMatrix_apply_self _ i⟩, fun i j hij => ?_⟩
  · exact minusMatrix_apply_eq_zero _ hji.ne' (fun h => (lt_asymm hji) h.1)
  · have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    exact minusMatrix_apply_eq_zero _ hne (fun h => (lt_asymm hij) h.2)

variable (n R)

/-- Multiplication `U_w⁺ × U_w⁻ → U`, plus factor on the left. -/
def mulMap (x : permutationUnipotentPlus n R w × permutationUnipotentMinus n R w) :
    upperUnipotent n R :=
  ⟨x.1.val * x.2.val,
    mul_mem (permutationUnipotentPlus_le_upperUnipotent n R w x.1.property)
      (permutationUnipotentMinus_le_upperUnipotent n R w x.2.property)⟩

/-- The factorization map `U → U_w⁺ × U_w⁻`. -/
def factorMap (g : upperUnipotent n R) :
    permutationUnipotentPlus n R w × permutationUnipotentMinus n R w :=
  (⟨plusUnit w g, plusUnit_mem w g⟩, ⟨minusUnit w g, minusUnit_mem w g⟩)

theorem mulMap_factorMap (g : upperUnipotent n R) :
    mulMap n R w (factorMap n R w g) = g :=
  Subtype.ext (Units.ext (plusMatrix_mul_minusMatrix g))

/-- Uniqueness of the factorization, from `U_w⁺ ⊓ U_w⁻ = ⊥`. -/
theorem mulMap_injective : Function.Injective (mulMap n R w) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' : a.val * b.val = a'.val * b'.val := congrArg Subtype.val h
  have hab : a'.val⁻¹ * a.val = b'.val * b.val⁻¹ :=
    calc a'.val⁻¹ * a.val = a'.val⁻¹ * (a.val * b.val) * b.val⁻¹ := by group
      _ = a'.val⁻¹ * (a'.val * b'.val) * b.val⁻¹ := by rw [h']
      _ = b'.val * b.val⁻¹ := by group
  have hc : a'.val⁻¹ * a.val ∈
      permutationUnipotentPlus n R w ⊓ permutationUnipotentMinus n R w :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a'.property) a.property,
        hab ▸ Subgroup.mul_mem _ b'.property (Subgroup.inv_mem _ b.property)⟩
  rw [permutationUnipotentPlus_inf_minus, Subgroup.mem_bot] at hc
  have h1 : a' = a := Subtype.ext (inv_mul_eq_one.mp hc)
  have h2 : b' = b := Subtype.ext (mul_inv_eq_one.mp (hab ▸ hc))
  rw [h1, h2]

section Topology

variable {n R w} [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_plusPart :
    Continuous (plusPart w : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R) := by
  refine continuous_matrix fun i j => ?_
  simp only [plusPart, Matrix.of_apply]
  split_ifs
  · exact continuous_id.matrix_elem i j
  · exact continuous_const

omit [IsTopologicalRing R] in
theorem continuous_minusPart :
    Continuous (minusPart w : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R) := by
  refine continuous_matrix fun i j => ?_
  simp only [minusPart, Matrix.of_apply]
  split_ifs
  · exact continuous_id.matrix_elem i j
  · exact continuous_const

theorem continuous_step :
    Continuous (fun p : Matrix (Fin n) (Fin n) R ×
        (Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R) => step w p.1 p.2) := by
  have h : Continuous (fun p : Matrix (Fin n) (Fin n) R ×
      (Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R) => p.1 - 1 - p.2.1 * p.2.2) :=
    (continuous_fst.sub continuous_const).sub
      ((continuous_fst.comp continuous_snd).matrix_mul (continuous_snd.comp continuous_snd))
  exact (continuous_plusPart.comp h).prodMk (continuous_minusPart.comp h)

theorem continuous_iterate_step
    (X : Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R) (m : ℕ) :
    Continuous (fun u : Matrix (Fin n) (Fin n) R => (step w u)^[m] X) := by
  induction m with
  | zero =>
    simp only [Function.iterate_zero_apply]
    exact continuous_const
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact continuous_step.comp (continuous_id.prodMk ih)

theorem continuous_strictParts :
    Continuous (strictParts w : Matrix (Fin n) (Fin n) R → _) :=
  continuous_iterate_step (0, 0) n

variable (n R w)

/-- The plus-minus multiplication homeomorphism `U_w⁺ × U_w⁻ ≃ₜ U`. -/
def homeomorph :
    (permutationUnipotentPlus n R w × permutationUnipotentMinus n R w) ≃ₜ
      upperUnipotent n R where
  toFun := mulMap n R w
  invFun := factorMap n R w
  left_inv x := mulMap_injective n R w (mulMap_factorMap n R w (mulMap n R w x))
  right_inv := mulMap_factorMap n R w
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hval : Continuous fun g : upperUnipotent n R => g.val.val :=
      Units.continuous_val.comp continuous_subtype_val
    have hinv : Continuous fun g : upperUnipotent n R =>
        (g.val⁻¹ : Langlands.GeneralLinear n R).val :=
      Units.continuous_coe_inv.comp continuous_subtype_val
    have hP : Continuous fun g : upperUnipotent n R => plusMatrix w g.val.val :=
      continuous_const.add (continuous_fst.comp (continuous_strictParts.comp hval))
    have hM : Continuous fun g : upperUnipotent n R => minusMatrix w g.val.val :=
      continuous_const.add (continuous_snd.comp (continuous_strictParts.comp hval))
    refine Continuous.prodMk ?_ ?_
    · apply Continuous.subtype_mk
      exact Units.continuous_iff.mpr ⟨hP, hM.matrix_mul hinv⟩
    · apply Continuous.subtype_mk
      exact Units.continuous_iff.mpr ⟨hM, hinv.matrix_mul hP⟩

theorem homeomorph_apply_val
    (x : permutationUnipotentPlus n R w × permutationUnipotentMinus n R w) :
    (homeomorph n R w x).val = x.1.val * x.2.val :=
  rfl

end Topology

end UpperUnipotentFactorization

/-- Every Hausdorff topological field, rank and permutation admits the
plus-minus multiplication homeomorphism `U_w⁺ × U_w⁻ ≃ₜ U`. -/
theorem upperUnipotentFactorization : UpperUnipotentFactorizationStatement.{u} := by
  intro K _ _ _ _ n w
  exact ⟨UpperUnipotentFactorization.homeomorph n K w,
    UpperUnipotentFactorization.homeomorph_apply_val n K w⟩

end Langlands.GeneralLinear
