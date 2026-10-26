import Langlands.Group.GL.CartanQuotientLawsStatement

/-!
# Intrinsic laws of concrete Cartan quotient cells

The algebraic laws use the actual central quotient and the published upper
Borel modulus. All rank-general lemmas include rank zero.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.GeneralLinear.CartanQuotient

universe uF

variable {p : ℕ} [Fact p.Prime]

theorem quotientMap_scalar (F : PadicField.{uF} p) (n : ℕ) (a : F.Carrierˣ) :
    quotientMap F n (GeneralLinear.scalar a) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (GeneralLinear.scalarToCenter a).property

theorem quotientMap_scalar_mul (F : PadicField.{uF} p) (n : ℕ)
    (a : F.Carrierˣ) (g : GeneralLinear n F.Carrier) :
    quotientMap F n (GeneralLinear.scalar a * g) = quotientMap F n g := by
  rw [map_mul, quotientMap_scalar, one_mul]

theorem quotientMap_mul_scalar (F : PadicField.{uF} p) (n : ℕ)
    (a : F.Carrierˣ) (g : GeneralLinear n F.Carrier) :
    quotientMap F n (g * GeneralLinear.scalar a) = quotientMap F n g := by
  rw [map_mul, quotientMap_scalar, mul_one]

variable {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

theorem subgroupCell_mono (H J : Subgroup (GeneralLinear n F.Carrier))
    (lam : Fin n → ℤ) (hHJ : H ≤ J) :
    subgroupCell T H lam ⊆ subgroupCell T J lam := by
  intro x hx
  rcases (mem_subgroupCell T H lam x).mp hx with ⟨h₁, hh₁, h₂, hh₂, hx⟩
  exact (mem_subgroupCell T J lam x).mpr
    ⟨h₁, hHJ hh₁, h₂, hHJ hh₂, hx⟩

theorem representative_shift (lam : Fin n → ℤ) (c : ℤ) :
    representative T (shift lam c) =
      GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T ^ c) *
        representative T lam := by
  apply Units.ext
  simp only [representative, Iwasawa.torus_val, Units.val_mul,
    GeneralLinear.scalar, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [shift, zpow_add, mul_comm]

theorem quotientMap_representative_shift (lam : Fin n → ℤ) (c : ℤ) :
    quotientMap F n (representative T (shift lam c)) =
      quotientMap F n (representative T lam) := by
  rw [representative_shift, quotientMap_scalar_mul]

theorem subgroupCell_shift (H : Subgroup (GeneralLinear n F.Carrier))
    (lam : Fin n → ℤ) (c : ℤ) :
    subgroupCell T H (shift lam c) = subgroupCell T H lam := by
  ext x
  simp only [mem_subgroupCell, map_mul, quotientMap_representative_shift]

theorem cell_shift (lam : Fin n → ℤ) (c : ℤ) :
    cell T (shift lam c) = cell T lam :=
  subgroupCell_shift T (maximalCompact T n) lam c

theorem degree_shift (lam : Fin n → ℤ) (c : ℤ) :
    degree (shift lam c) = degree lam := by
  simp [degree, shift]

theorem delta_shift (lam : Fin n → ℤ) (c : ℤ) :
    delta T (shift lam c) = delta T lam := by
  simp only [delta, degree_shift]

theorem degree_nonneg (lam : Fin n → ℤ) (hlam : Antitone lam) :
    0 ≤ degree lam := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j hj
  exact sub_nonneg.mpr (hlam (Finset.mem_filter.mp hj).2.le)

theorem delta_pos (lam : Fin n → ℤ) : 0 < delta T lam := by
  apply zpow_pos
  exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)

theorem height_pos (lam : Fin n → ℤ) : 0 < height lam := by
  unfold height
  positivity

theorem representative_diagonal_abs (lam : Fin n → ℤ) (i : Fin n) :
    T.normalizedAbs (representative T lam i i) =
      (T.residueCardinality : ℝ) ^ (-lam i) := by
  change T.normalizedAbs
    ((Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit T) lam).val i i) = _
  rw [Iwasawa.torus_val, Matrix.diagonal_apply_eq,
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs]

theorem representative_offDiagonal (lam : Fin n → ℤ) (i j : Fin n)
    (hij : i ≠ j) : representative T lam i j = 0 := by
  change (Iwasawa.torus (LocalFactor.PadicAbelian.uniformizerUnit T) lam).val i j = 0
  rw [Iwasawa.torus_val, Matrix.diagonal_apply_ne _ hij]

theorem representative_diagonal_abs_monotone (lam : Fin n → ℤ)
    (hlam : Antitone lam) :
    Monotone (fun i => T.normalizedAbs (representative T lam i i)) := by
  intro i j hij
  calc
    T.normalizedAbs (representative T lam i i) =
        (T.residueCardinality : ℝ) ^ (-lam i) := representative_diagonal_abs T lam i
    _ ≤ (T.residueCardinality : ℝ) ^ (-lam j) :=
      zpow_le_zpow_right₀ (by exact_mod_cast T.residueCardinality_gt_one.le)
        (neg_le_neg (hlam hij))
    _ = T.normalizedAbs (representative T lam j j) :=
      (representative_diagonal_abs T lam j).symm

theorem representativeLevi_val (lam : Fin n → ℤ) :
    ((BlockShape.singletons n).leviEmbedding F.Carrier
      (representativeLevi T lam)).val = (representative T lam).val := by
  exact BlockShape.leviEmbedding_singletonLevi_val F.Carrier _

theorem representativeBorel_val (lam : Fin n → ℤ) :
    ((representativeBorel T lam : GeneralLinear n F.Carrier)).val =
      (representative T lam).val :=
  representativeLevi_val T lam

private theorem real_zpow_sum {ι : Type*} (s : Finset ι) (q : ℝ)
    (hq : q ≠ 0) (f : ι → ℤ) :
    q ^ (∑ i ∈ s, f i) = ∏ i ∈ s, q ^ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hq, ih]

theorem delta_eq_leviModulus (lam : Fin n → ℤ) :
    delta T lam =
      ((T.leviModulus (BlockShape.singletons n) (representativeLevi T lam) :
        ℝ≥0) : ℝ) := by
  have hq : (T.residueCardinality : ℝ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
  calc
    delta T lam =
        ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
          (T.residueCardinality : ℝ) ^ (-(lam i - lam j)) := by
      unfold delta degree
      rw [← Finset.sum_neg_distrib, real_zpow_sum _ _ hq]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.sum_neg_distrib, real_zpow_sum _ _ hq]
    _ = _ := by
      rw [representativeLevi, T.leviModulus_singletonLevi]
      simp only [Units.coe_prod, NNReal.coe_prod, Units.val_div_eq_div_val, NNReal.coe_div,
        T.normalizedAbsUnits_coe, LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs]
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_sub₀ hq]
      congr 1
      omega

theorem delta_eq_parabolicModulus (lam : Fin n → ℤ) :
    delta T lam =
      ((T.parabolicModulus (BlockShape.singletons n) (representativeBorel T lam) :
        ℝ≥0) : ℝ) := by
  simpa only [representativeBorel, T.parabolicModulus_section] using
    delta_eq_leviModulus T lam

theorem normalized_iff_antitone_last_eq_zero (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    Normalized lam ↔ Antitone lam ∧ lam (Fin.last m) = 0 := by
  constructor
  · rintro ⟨hanti, hnonneg, i, hi⟩
    refine ⟨hanti, le_antisymm ?_ (hnonneg _)⟩
    calc
      lam (Fin.last m) ≤ lam i := hanti (Fin.le_last i)
      _ = 0 := hi
  · rintro ⟨hanti, hlast⟩
    refine ⟨hanti, ?_, Fin.last m, hlast⟩
    intro i
    simpa only [hlast] using hanti (Fin.le_last i)

theorem normalized_one_iff (lam : Fin 1 → ℤ) : Normalized lam ↔ lam = 0 := by
  rw [normalized_iff_antitone_last_eq_zero 0]
  constructor
  · intro h
    funext i
    have hi : i = Fin.last 0 := Subsingleton.elim _ _
    simpa only [hi, Pi.zero_apply] using h.2
  · rintro rfl
    exact ⟨antitone_const, rfl⟩

/-- The exact closed proposition of intrinsic laws, over every field universe. -/
theorem cartanQuotientLaws : CartanQuotientLawsStatement.{uF} := by
  intro p _ F T
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ => mem_cell T, fun _ => mem_subgroupCell T,
      fun _ => subgroupCell_mono T⟩
  · exact ⟨quotientMap_scalar F, quotientMap_scalar_mul F, quotientMap_mul_scalar F,
      fun _ => representative_shift T, fun _ => quotientMap_representative_shift T,
      fun _ => subgroupCell_shift T, fun _ => cell_shift T⟩
  · exact ⟨fun _ => degree_shift, fun _ => delta_shift T, fun _ => degree_nonneg,
      fun _ => delta_pos T, fun _ => height_pos⟩
  · exact ⟨fun _ => representative_diagonal_abs T, fun _ => representative_offDiagonal T,
      fun _ => representative_diagonal_abs_monotone T⟩
  · exact ⟨fun _ => representativeLevi_val T, fun _ => representativeBorel_val T,
      fun _ => delta_eq_leviModulus T, fun _ => delta_eq_parabolicModulus T⟩
  · exact ⟨normalized_iff_antitone_last_eq_zero, normalized_one_iff,
      fun _ => inferInstance⟩

end Langlands.GeneralLinear.CartanQuotient
