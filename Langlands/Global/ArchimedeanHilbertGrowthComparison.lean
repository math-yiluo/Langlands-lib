import Langlands.Global.ArchimedeanHilbertGrowthComparisonStatement

noncomputable section
universe u
open scoped Classical NNReal Matrix.Norms.Operator

namespace Langlands.Global
open NumberField NumberField.InfinitePlace

private theorem sum3_nonneg {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (a : α → β → γ → ℝ) (ha : ∀ x y z, 0 ≤ a x y z) :
    0 ≤ ∑ x, ∑ y, ∑ z, a x y z :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    Finset.sum_nonneg fun z _ => ha x y z

private theorem term_le_sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (a : α → β → γ → ℝ) (ha : ∀ x y z, 0 ≤ a x y z) (x : α) (y : β) (z : γ) :
    a x y z ≤ ∑ x, ∑ y, ∑ z, a x y z := by
  exact (Finset.single_le_sum (fun z _ => ha x y z) (Finset.mem_univ z)).trans
    ((Finset.single_le_sum (fun y _ => Finset.sum_nonneg fun z _ => ha x y z)
      (Finset.mem_univ y)).trans
      (Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun y _ =>
        Finset.sum_nonneg fun z _ => ha x y z) (Finset.mem_univ x)))

private theorem norm_entry_le_rowNorm {α ι : Type*} [Fintype ι]
    [SeminormedAddCommGroup α] (A : Matrix ι ι α) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i))
  exact_mod_cast h

private theorem rowNorm_le_card_mul {α ι : Type*} [Fintype ι]
    [SeminormedAddCommGroup α] (A : Matrix ι ι α) (r : ℝ) (hr : 0 ≤ r)
    (hA : ∀ i j, ‖A i j‖ ≤ r) : ‖A‖ ≤ Fintype.card ι * r := by
  let R : NNReal := ⟨r, hr⟩
  have h : ‖A‖₊ ≤ (Fintype.card ι : NNReal) * R := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    have hs : (∑ j, ‖A i j‖₊) ≤ ∑ _j : ι, R := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast hA i j
    simpa using hs
  exact_mod_cast h

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private theorem localEntrySq_nonneg (g : InfiniteAdelicGL K n) :
    0 ≤ infiniteAdelicLocalEntrySq K n g :=
  add_nonneg (sum3_nonneg _ (fun _ _ _ => sq_nonneg _))
    (sum3_nonneg _ (fun _ _ _ => sq_nonneg _))

private theorem localEntrySq_le_hilbert_sq (g : InfiniteAdelicGL K n) :
    infiniteAdelicLocalEntrySq K n g ≤ infiniteAdelicHilbertNorm K n g ^ 2 := by
  rw [infiniteAdelicHilbertNorm_sq]
  linarith [localEntrySq_nonneg K n g⁻¹]

private theorem mixed_entry_le_hilbert (g : InfiniteAdelicGL K n) (i j : Fin n) :
    ‖(archimedeanGLCoordinates K n g).val i j‖ ≤ infiniteAdelicHilbertNorm K n g := by
  have hpos := (infiniteAdelicHilbertNorm_pos K n g).le
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hpos).mpr
    intro v
    have ht := term_le_sum3
      (fun v i j => ‖ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2)
      (fun _ _ _ => sq_nonneg _) v i j
    have hs : 0 ≤ ∑ v, ∑ i, ∑ j,
        ‖ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2 :=
      sum3_nonneg _ (fun _ _ _ => sq_nonneg _)
    have hb := localEntrySq_le_hilbert_sq K n g
    unfold infiniteAdelicLocalEntrySq at hb
    change ‖ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ≤ _
    nlinarith [norm_nonneg (ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v i j)]
  · apply (pi_norm_le_iff_of_nonneg hpos).mpr
    intro v
    have ht := term_le_sum3
      (fun v i j => ‖ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2)
      (fun _ _ _ => sq_nonneg _) v i j
    have hs : 0 ≤ ∑ v, ∑ i, ∑ j,
        ‖ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2 :=
      sum3_nonneg _ (fun _ _ _ => sq_nonneg _)
    have hb := localEntrySq_le_hilbert_sq K n g
    unfold infiniteAdelicLocalEntrySq at hb
    change ‖ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ≤ _
    nlinarith [norm_nonneg (ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v i j)]

private theorem matrixHeight_le_hilbert (g : InfiniteAdelicGL K n) :
    ArchimedeanGL.matrixHeight K n g ≤ (n + 1 : ℝ) * infiniteAdelicHilbertNorm K n g := by
  have hp := (infiniteAdelicHilbertNorm_pos K n g).le
  have hval := rowNorm_le_card_mul (archimedeanGLCoordinates K n g).val _ hp
    (mixed_entry_le_hilbert K n g)
  have hinv := rowNorm_le_card_mul (archimedeanGLCoordinates K n g⁻¹).val _
    (infiniteAdelicHilbertNorm_pos K n g⁻¹).le (mixed_entry_le_hilbert K n g⁻¹)
  simp only [Fintype.card_fin, infiniteAdelicHilbertNorm_inv, map_inv] at hval hinv
  change ‖(archimedeanGLCoordinates K n g).inv‖ ≤ (n : ℝ) * infiniteAdelicHilbertNorm K n g at hinv
  apply max_le
  · nlinarith [one_le_infiniteAdelicHilbertNorm K n g, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hp]
  · apply max_le <;> linarith

private theorem localEntrySq_le_height (g : InfiniteAdelicGL K n) :
    infiniteAdelicLocalEntrySq K n g ≤
      ((Fintype.card {v : InfinitePlace K // IsReal v} : ℝ) +
        Fintype.card {v : InfinitePlace K // IsComplex v}) * n * n *
          ArchimedeanGL.matrixHeight K n g ^ 2 := by
  have hentry (i j : Fin n) :
      ‖(archimedeanGLCoordinates K n g).val i j‖ ≤ ArchimedeanGL.matrixHeight K n g :=
    (norm_entry_le_rowNorm _ i j).trans (ArchimedeanGL.norm_val_le_matrixHeight K n g)
  have hr (v : {v : InfinitePlace K // IsReal v}) (i j : Fin n) :
      ‖ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2 ≤
        ArchimedeanGL.matrixHeight K n g ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_le_pi_norm _ v).trans ((norm_fst_le _).trans (hentry i j))
  have hc (v : {v : InfinitePlace K // IsComplex v}) (i j : Fin n) :
      ‖ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v i j‖ ^ 2 ≤
        ArchimedeanGL.matrixHeight K n g ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_le_pi_norm _ v).trans ((norm_snd_le _).trans (hentry i j))
  calc
    infiniteAdelicLocalEntrySq K n g ≤
        (∑ _v : {v : InfinitePlace K // IsReal v}, ∑ _i : Fin n, ∑ _j : Fin n,
          ArchimedeanGL.matrixHeight K n g ^ 2) +
        (∑ _v : {v : InfinitePlace K // IsComplex v}, ∑ _i : Fin n, ∑ _j : Fin n,
          ArchimedeanGL.matrixHeight K n g ^ 2) := by
      exact add_le_add
        (Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => hr v i j)
        (Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => hc v i j)
    _ = _ := by simp; ring

/-- Uniform linear comparison of the published concrete matrix and Hilbert norms. -/
theorem archimedeanMatrixHilbertComparison :
    ArchimedeanMatrixHilbertComparisonStatement K n := by
  let m : ℝ := ((Fintype.card {v : InfinitePlace K // IsReal v} : ℝ) +
    Fintype.card {v : InfinitePlace K // IsComplex v}) * n * n
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hd : 0 < 1 + 2 * m := by positivity
  refine ⟨n + 1, Real.sqrt (1 + 2 * m), by positivity, Real.sqrt_pos.mpr hd, ?_⟩
  intro g
  refine ⟨matrixHeight_le_hilbert K n g, ?_⟩
  have hforward : infiniteAdelicLocalEntrySq K n g ≤ m * ArchimedeanGL.matrixHeight K n g ^ 2 :=
    localEntrySq_le_height K n g
  have hinverse := localEntrySq_le_height K n g⁻¹
  rw [ArchimedeanGL.matrixHeight_inv] at hinverse
  change infiniteAdelicLocalEntrySq K n g⁻¹ ≤ m * ArchimedeanGL.matrixHeight K n g ^ 2 at hinverse
  have hsq : infiniteAdelicHilbertNorm K n g ^ 2 ≤
      (Real.sqrt (1 + 2 * m) * ArchimedeanGL.matrixHeight K n g) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hd.le, infiniteAdelicHilbertNorm_sq]
    nlinarith [ArchimedeanGL.one_le_matrixHeight K n g]
  exact (sq_le_sq₀ (infiniteAdelicHilbertNorm_pos K n g).le
    (mul_nonneg (Real.sqrt_nonneg _) (ArchimedeanGL.matrixHeight_nonneg K n g))).mp hsq

/-- Polynomial growth is unchanged for every function after changing the concrete norm. -/
theorem archimedeanHilbertGrowthEquivalence :
    ArchimedeanHilbertGrowthEquivalenceStatement K n := by
  obtain ⟨C, D, hC, hD, hcompare⟩ := archimedeanMatrixHilbertComparison K n
  intro f
  constructor
  · rintro ⟨B, hB, d, hf⟩
    refine ⟨B * C ^ d, mul_nonneg hB (pow_nonneg hC.le _), d, ?_⟩
    intro g
    calc
      ‖f g‖ ≤ B * ArchimedeanGL.matrixHeight K n g ^ d := hf g
      _ ≤ B * (C * infiniteAdelicHilbertNorm K n g) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (ArchimedeanGL.matrixHeight_nonneg K n g) (hcompare g).1 d) hB
      _ = (B * C ^ d) * infiniteAdelicHilbertNorm K n g ^ d := by rw [mul_pow, mul_assoc]
  · rintro ⟨B, hB, d, hf⟩
    refine ⟨B * D ^ d, mul_nonneg hB (pow_nonneg hD.le _), d, ?_⟩
    intro g
    calc
      ‖f g‖ ≤ B * infiniteAdelicHilbertNorm K n g ^ d := hf g
      _ ≤ B * (D * ArchimedeanGL.matrixHeight K n g) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (infiniteAdelicHilbertNorm_pos K n g).le (hcompare g).2 d) hB
      _ = (B * D ^ d) * ArchimedeanGL.matrixHeight K n g ^ d := by rw [mul_pow, mul_assoc]

/-- The comparison is applied independently after fixing each finite adelic slice. -/
theorem adelicHilbertGrowthEquivalence :
    AdelicHilbertGrowthEquivalenceStatement K n := by
  intro f
  exact forall_congr' fun b => archimedeanHilbertGrowthEquivalence K n
    (Langlands.Automorphic.infiniteSlice K n b f)

/-- Exact published aggregate, in arbitrary universe and at every natural rank. -/
theorem archimedeanHilbertGrowthComparison :
    ArchimedeanHilbertGrowthComparisonStatement K n :=
  ⟨archimedeanMatrixHilbertComparison K n, archimedeanHilbertGrowthEquivalence K n,
    adelicHilbertGrowthEquivalence K n⟩

end Langlands.Global
