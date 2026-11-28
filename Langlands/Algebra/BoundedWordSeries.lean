import Langlands.Algebra.CyclicWordSplitting
import Langlands.Algebra.FormalExponentialTrace

/-! # Coefficient bounds for graded word series -/

noncomputable section

namespace Langlands.CyclicWords

open FreeMonoid PowerSeries Finset Langlands.FormalPowerSeries

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

/-- The words of a polynomial have one length, and every coefficient has a common norm bound. -/
structure WordPolynomialControl (n : ℕ) (c : ℝ) (p : WordPolynomial F) : Prop where
  graded : HasWordLength F p n
  norm_le : ∀ w, ‖p.coeff w‖ ≤ c

namespace WordPolynomialControl

variable {n m : ℕ} {a b c : ℝ} {p q : WordPolynomial F}

omit [IsUltrametricDist F] in
theorem nonneg (hp : WordPolynomialControl n c p) : 0 ≤ c := (norm_nonneg _).trans (hp.norm_le 1)

omit [IsUltrametricDist F] in
theorem zero (n : ℕ) (hc : 0 ≤ c) : WordPolynomialControl n c (0 : WordPolynomial F) :=
  ⟨fun _ _ => rfl, fun _ => by simpa using hc⟩

omit [IsUltrametricDist F] in
theorem single (w : Word) (z : F) : WordPolynomialControl w.length ‖z‖ (MonoidAlgebra.single w z) := by
  classical
  refine ⟨?_, ?_⟩
  · intro v hv
    change Finsupp.single w z v = 0
    rw [Finsupp.single_apply, ite_eq_right (fun h => hv (congrArg FreeMonoid.length h.symm))]
  · intro v
    change ‖Finsupp.single w z v‖ ≤ ‖z‖
    rw [Finsupp.single_apply]
    split <;> simp

omit [IsUltrametricDist F] in
theorem mono (hp : WordPolynomialControl n a p) (hle : a ≤ b) : WordPolynomialControl n b p :=
  ⟨hp.graded, fun w => (hp.norm_le w).trans hle⟩

theorem add (hp : WordPolynomialControl n c p) (hq : WordPolynomialControl n c q) :
    WordPolynomialControl n c (p + q) := by
  refine ⟨fun w hw => by simp [hp.graded w hw, hq.graded w hw], fun w => ?_⟩
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hp.norm_le w) (hq.norm_le w))

omit [IsUltrametricDist F] in
theorem neg (hp : WordPolynomialControl n c p) : WordPolynomialControl n c (-p) :=
  ⟨fun w hw => by simp [hp.graded w hw], fun w => by simpa using hp.norm_le w⟩

theorem sub (hp : WordPolynomialControl n c p) (hq : WordPolynomialControl n c q) :
    WordPolynomialControl n c (p - q) := by simpa only [sub_eq_add_neg] using hp.add hq.neg

omit [IsUltrametricDist F] in
theorem smul (hp : WordPolynomialControl n c p) (d : F) : WordPolynomialControl n (‖d‖ * c) (d • p) := by
  refine ⟨fun w hw => by simp [hp.graded w hw], fun w => ?_⟩
  rw [MonoidAlgebra.coeff_smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hp.norm_le w) (norm_nonneg _)

theorem finsetSum {ι : Type*} {s : Finset ι} {f : ι → WordPolynomial F} (hc : 0 ≤ c)
    (h : ∀ i ∈ s, WordPolynomialControl n c (f i)) : WordPolynomialControl n c (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (F := F) n hc
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem mul (hp : WordPolynomialControl n a p) (hq : WordPolynomialControl m b q) :
    WordPolynomialControl (n + m) (a * b) (p * q) := by
  classical
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [MonoidAlgebra.coeff_mul]
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro v hv
    have hun := not_ne_iff.mp (fun h => (Finsupp.mem_support_iff.mp hu) (hp.graded u h))
    have hvm := not_ne_iff.mp (fun h => (Finsupp.mem_support_iff.mp hv) (hq.graded v h))
    refine ite_eq_right fun h => hw ?_
    rw [← h, length_mul, hun, hvm]
  · intro w
    rw [MonoidAlgebra.coeff_mul]
    have hab := mul_nonneg hp.nonneg hq.nonneg
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hab
    intro u _
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hab
    intro v _
    change ‖(if u * v = w then p.coeff u * q.coeff v else 0)‖ ≤ a * b
    split
    · rw [norm_mul]
      exact mul_le_mul (hp.norm_le u) (hq.norm_le v) (norm_nonneg _) hp.nonneg
    · simpa using hab

end WordPolynomialControl

/-- Each coefficient has word length equal to its series degree and the same norm bound. -/
def WordSeriesControl (c : ℝ) (f : PowerSeries (WordPolynomial F)) : Prop :=
  ∀ n : ℕ, WordPolynomialControl n c (coeff n f)

namespace WordSeriesControl

variable {a b c : ℝ} {f g : PowerSeries (WordPolynomial F)}

omit [IsUltrametricDist F] in
theorem nonneg (hf : WordSeriesControl c f) : 0 ≤ c := (hf 0).nonneg

omit [IsUltrametricDist F] in
theorem monomial {n : ℕ} {p : WordPolynomial F} (hp : WordPolynomialControl n c p) :
    WordSeriesControl c (PowerSeries.monomial n p) := by
  intro m
  rw [coeff_monomial]
  split
  · subst m; exact hp
  · exact WordPolynomialControl.zero _ hp.nonneg

omit [IsUltrametricDist F] in
theorem one : WordSeriesControl 1 (1 : PowerSeries (WordPolynomial F)) := by
  have h := monomial (WordPolynomialControl.single (1 : Word) (1 : F))
  simpa only [length_one, norm_one, PowerSeries.monomial_zero_eq_C_apply, ← MonoidAlgebra.one_def,
    map_one] using h

omit [IsUltrametricDist F] in
theorem mono (hf : WordSeriesControl a f) (hle : a ≤ b) : WordSeriesControl b f := fun n => (hf n).mono hle

theorem add (hf : WordSeriesControl c f) (hg : WordSeriesControl c g) : WordSeriesControl c (f + g) :=
  fun n => by simpa only [map_add] using (hf n).add (hg n)

theorem sub (hf : WordSeriesControl c f) (hg : WordSeriesControl c g) : WordSeriesControl c (f - g) :=
  fun n => by simpa only [map_sub] using (hf n).sub (hg n)

omit [IsUltrametricDist F] in
theorem smul (hf : WordSeriesControl c f) (z : F) : WordSeriesControl (‖z‖ * c) (z • f) :=
  fun n => by simpa only [coeff_smul] using (hf n).smul z

theorem mul (hf : WordSeriesControl a f) (hg : WordSeriesControl b g) : WordSeriesControl (a * b) (f * g) := by
  intro n
  rw [coeff_mul]
  apply WordPolynomialControl.finsetSum (mul_nonneg hf.nonneg hg.nonneg)
  intro p hp
  exact Finset.mem_antidiagonal.mp hp ▸ (hf p.1).mul (hg p.2)

theorem pow (hf : WordSeriesControl c f) (n : ℕ) : WordSeriesControl (c ^ n) (f ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using one (F := F)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem invOfUnit (hf : WordSeriesControl 1 f) : WordSeriesControl 1 (PowerSeries.invOfUnit f 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · subst n
      simpa only [inv_one, Units.val_one, ← MonoidAlgebra.one_def, norm_one, length_one] using
        WordPolynomialControl.single (1 : Word) (1 : F)
    · simp only [inv_one, Units.val_one, neg_mul, one_mul]
      apply WordPolynomialControl.neg
      apply WordPolynomialControl.finsetSum zero_le_one
      intro p hp
      split_ifs with hp₂
      · have h := (hf p.1).mul (ih p.2 hp₂)
        rw [Finset.mem_antidiagonal.mp hp, one_mul] at h
        exact h
      · exact WordPolynomialControl.zero _ zero_le_one

/-- If every positive factorial term is bounded by `c`, the degreewise factorial sum
differs from one by a series with that bound. Degree `n` uses powers `0` through `n`
for any input constant coefficient. This is the usual formal exponential over a
characteristic-zero field when the exponent has zero constant coefficient. -/
def ExponentialControlStatement (f : PowerSeries (WordPolynomial F)) (c : ℝ) : Prop :=
  WordSeriesControl c f → (∀ k : ℕ, 0 < k → ‖((k.factorial : F)⁻¹)‖ * c ^ k ≤ c) →
  WordSeriesControl c (formalExponential F f - 1)

theorem exponentialControl (f : PowerSeries (WordPolynomial F)) (c : ℝ) : ExponentialControlStatement f c := by
  intro hf hFactorial n
  simp only [formalExponential, exponentialPartial, coeff_mk, map_sub]
  rw [Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, map_add, add_sub_cancel_right, map_sum,
    coeff_smul]
  apply WordPolynomialControl.finsetSum hf.nonneg
  intro k _
  exact (((hf.pow (k + 1)) n).smul ((Nat.factorial (k + 1) : F)⁻¹)).mono (hFactorial _ (Nat.succ_pos k))

/-- Products of series differing from one by coefficients bounded by `c ≤ 1` preserve the bound. -/
theorem mul_sub_one (hc : c ≤ 1) (hf : WordSeriesControl c (f - 1)) (hg : WordSeriesControl c (g - 1)) :
    WordSeriesControl c (f * g - 1) := by
  have h := ((hf.mul hg).mono (mul_le_of_le_one_right hf.nonneg hc)).add (hf.add hg)
  have he : (f - 1) * (g - 1) + (f - 1 + (g - 1)) = f * g - 1 := by
    simp only [mul_sub, sub_mul, one_mul, mul_one]
    abel
  rwa [he] at h

end WordSeriesControl

end Langlands.CyclicWords
