import Langlands.Representation.Classification.ProductLeviNecessityCombinatorics

/-!
# Test elements for the necessity of the upper Jacquet bounds

Facts about the block scalar tuples `testScalars`: weak contraction, their
block matrices, centrality of the full ones, and their refined moduli.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.ProductLeviNecessity

open GeneralLinear Geometric ProductLeviChamber

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### Block scalars with prescribed valuations -/

section Valuation

variable {N : ℕ} (B : BlockShape N)

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ℝ) (ha : a ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ ha]

/-- Block scalars with absolute values `q ^ (-f l)` and `f` antitone are weakly contracting. -/
theorem isWeaklyContracting_of_abs (c : Fin B.length → F.Carrierˣ) (f : Fin B.length → ℤ)
    (hf : ∀ l, T.normalizedAbs (c l : F.Carrier) = (T.residueCardinality : ℝ) ^ (-f l))
    (hanti : ∀ l l', l < l' → f l' ≤ f l) : B.IsWeaklyContracting T c := by
  intro l l' hll'
  have hq := residueCardinality_gt_one_real T
  rw [BlockShape.blockScalarRatio_apply, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv, T.normalizedAbsUnits_coe,
    T.normalizedAbsUnits_coe, hf, hf, ← zpow_neg, ← zpow_add₀ (by positivity)]
  apply zpow_le_one_of_nonpos₀ hq.le
  linarith [hanti l l' hll']

/-- The modulus of block scalars with absolute values `q ^ (-f l)`. -/
theorem leviModulus_blockScalarLevi_of_abs (c : Fin B.length → F.Carrierˣ)
    (f : Fin B.length → ℤ)
    (hf : ∀ l, T.normalizedAbs (c l : F.Carrier) = (T.residueCardinality : ℝ) ^ (-f l)) :
    ((T.leviModulus B (B.blockScalarLevi F.Carrier c) : ℝ≥0) : ℝ) =
      (T.residueCardinality : ℝ) ^ (-∑ l, ∑ l' ∈ Finset.univ.filter (fun l' => l < l'),
        (f l - f l') * ((B.size l * B.size l' : ℕ) : ℤ)) := by
  have hq0 : (T.residueCardinality : ℝ) ≠ 0 :=
    (zero_lt_one.trans (residueCardinality_gt_one_real T)).ne'
  rw [T.leviModulus_apply, Units.coe_prod, NNReal.coe_prod, ← Finset.sum_neg_distrib,
    ← prod_zpow_eq_zpow_sum _ _ hq0]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Units.coe_prod, NNReal.coe_prod, ← Finset.sum_neg_distrib,
    ← prod_zpow_eq_zpow_sum _ _ hq0]
  refine Finset.prod_congr rfl fun l' _ => ?_
  rw [Units.val_div_eq_div_val, NNReal.coe_div, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, NNReal.coe_pow, NNReal.coe_pow, BlockShape.blockScalarLevi_apply,
    BlockShape.blockScalarLevi_apply, T.determinantNorm_scalar, T.determinantNorm_scalar,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, NNReal.coe_pow, NNReal.coe_pow,
    T.normalizedAbsUnits_coe, T.normalizedAbsUnits_coe, hf, hf, ← pow_mul, ← pow_mul,
    ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_sub₀ hq0]
  congr 1
  push_cast
  ring

/-- The number of coordinates whose block satisfies a predicate. -/
theorem card_filter_block (P : Fin B.length → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : Fin N => P (B.indexEquiv.symm x).1).card =
      ∑ l, if P l then B.size l else 0 := by
  rw [Finset.card_filter, ← B.indexEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

end Valuation

/-! ### The test tuples -/

variable {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)

/-- Indices of block j lying in refined blocks of index below k. -/
def testSet (j : Fin C.length) (k : ℕ) : Finset (Fin (C.size j)) :=
  Finset.univ.filter fun x => ((D j).indexEquiv.symm x).1.val < k

theorem testScalars_of_ne (j : Fin C.length) (k : ℕ) (e : ℤ) {i : Fin C.length} (h : i ≠ j) :
    testScalars T C D j k e i = 1 := by
  funext l
  simp [testScalars, h]

theorem testScalars_same (j : Fin C.length) (k : ℕ) (e : ℤ) (l : Fin (D j).length) :
    testScalars T C D j k e j l =
      if l.val < k then LocalFactor.PadicAbelian.uniformizerUnit T ^ e else 1 := by
  simp [testScalars]

theorem testScalars_full (j : Fin C.length) (e : ℤ) :
    testScalars T C D j (D j).length e j =
      fun _ => LocalFactor.PadicAbelian.uniformizerUnit T ^ e := by
  funext l
  simp [testScalars, l.isLt]

theorem testScalars_abs (j : Fin C.length) (k : ℕ) (l : Fin (D j).length) :
    T.normalizedAbs (testScalars T C D j k 1 j l : F.Carrier) =
      (T.residueCardinality : ℝ) ^ (-(if l.val < k then (1 : ℤ) else 0)) := by
  rw [testScalars_same]
  split_ifs
  · exact LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T 1
  · simp [T.normalizedAbs_one]

theorem testScalars_isWeaklyContracting (j : Fin C.length) (k : ℕ) (i : Fin C.length) :
    (D i).IsWeaklyContracting T (testScalars T C D j k 1 i) := by
  by_cases h : i = j
  · subst h
    refine isWeaklyContracting_of_abs T (D i) _ (fun l => if l.val < k then 1 else 0)
      (testScalars_abs T C D i k) fun l l' hll' => ?_
    have : l.val < l'.val := hll'
    split_ifs <;> omega
  · rw [testScalars_of_ne T C D j k 1 h]
    exact BlockShape.isWeaklyContracting_one _ T

theorem testScalars_full_isWeaklyContracting (j : Fin C.length) (e : ℤ) (i : Fin C.length) :
    (D i).IsWeaklyContracting T (testScalars T C D j (D j).length e i) := by
  by_cases h : i = j
  · subst h
    rw [testScalars_full]
    refine isWeaklyContracting_of_abs T (D i) _ (fun _ => e)
      (fun _ => LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T e) fun _ _ _ => le_rfl
  · rw [testScalars_of_ne T C D j _ e h]
    exact BlockShape.isWeaklyContracting_one _ T

theorem testScalars_blockScalar_same (j : Fin C.length) (k : ℕ) :
    ((D j).blockScalar F.Carrier (testScalars T C D j k 1 j) :
        Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
      Matrix.diagonal (fun a => if a ∈ testSet C D j k then T.uniformizer else 1) := by
  rw [ProductLeviChamber.blockScalar_val]
  congr 1
  funext x
  rw [testScalars_same]
  simp only [testSet, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp

theorem testScalars_blockScalar_ne (j : Fin C.length) (k : ℕ) (e : ℤ) {i : Fin C.length}
    (h : i ≠ j) : (D i).blockScalar F.Carrier (testScalars T C D j k e i) = 1 := by
  rw [testScalars_of_ne T C D j k e h, BlockShape.blockScalar_one]

/-- The refined Levi blocks of a flattened test element. -/
theorem refinedLeviBlock_test (c : ∀ i, Fin (D i).length → F.Carrierˣ) (i : Fin C.length) :
    PadicField.TopologicalData.refinedLeviBlock C D i (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) =
      (D i).blockScalarLevi F.Carrier (c i) := by
  rw [PadicField.TopologicalData.refinedLeviBlock_flattenedLeviEquiv,
    Geometric.flattenedLeviProductEquiv_blockScalarLevi]
  congr 1
  funext l
  exact flatScalars_apply C D c i l

theorem testSet_card (j : Fin C.length) (k : ℕ) :
    (testSet C D j k).card = ∑ l, if l.val < k then (D j).size l else 0 :=
  card_filter_block (D j) (fun l => l.val < k)

theorem testSet_compl_card (j : Fin C.length) (k : ℕ) :
    (testSet C D j k)ᶜ.card = ∑ l, if ¬ l.val < k then (D j).size l else 0 := by
  rw [testSet, Finset.compl_filter]
  exact card_filter_block (D j) (fun l => ¬ l.val < k)

theorem testScalars_refinedLeviModulus (j : Fin C.length) (k : ℕ) :
    ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D (testScalars T C D j k 1)))) :
          ℝ≥0) : ℝ) =
      (T.residueCardinality : ℝ) ^
        (-(((testSet C D j k).card * (testSet C D j k)ᶜ.card : ℕ) : ℤ)) := by
  rw [T.refinedLeviModulus_apply]
  simp only [refinedLeviBlock_test]
  rw [Finset.prod_eq_single j]
  · rw [leviModulus_blockScalarLevi_of_abs T (D j) _ (fun l => if l.val < k then 1 else 0)
      (testScalars_abs T C D j k)]
    congr 2
    rw [testSet_card, testSet_compl_card]
    push_cast
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l' _ => ?_
    have h : l < l' ↔ l.val < l'.val := Iff.rfl
    by_cases hll' : l < l'
    · have := h.mp hll'
      simp only [hll', ↓reduceIte]
      split_ifs <;> omega
    · have : ¬ l.val < l'.val := fun h' => hll' (h.mpr h')
      simp only [hll', ↓reduceIte]
      split_ifs <;> omega
  · intro i _ hi
    rw [testScalars_of_ne T C D j k 1 hi, map_one, map_one]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem testScalars_full_mem_center (j : Fin C.length) (e : ℤ) :
    (fun i => (D i).blockScalar F.Carrier (testScalars T C D j (D j).length e i) :
        C.Levi F.Carrier) ∈ Subgroup.center (C.Levi F.Carrier) := by
  rw [Subgroup.center_pi, Subgroup.mem_pi]
  intro i _
  by_cases h : i = j
  · subst h
    rw [testScalars_full]
    have hs : (D i).blockScalar F.Carrier (fun _ => LocalFactor.PadicAbelian.uniformizerUnit T ^ e)
        = GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T ^ e) := by
      apply Units.ext
      rw [ProductLeviChamber.blockScalar_val, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply]
    rw [hs]
    exact (GeneralLinear.scalarToCenter (LocalFactor.PadicAbelian.uniformizerUnit T ^ e)).property
  · rw [testScalars_blockScalar_ne T C D j _ e h]
    exact Subgroup.one_mem _

theorem testScalars_full_refinedLeviModulus (j : Fin C.length) (e : ℤ) :
    ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier
          (flatScalars C D (testScalars T C D j (D j).length e)))) : ℝ≥0) : ℝ) = 1 := by
  rw [T.refinedLeviModulus_apply]
  simp only [refinedLeviBlock_test]
  rw [Finset.prod_eq_single j]
  · rw [leviModulus_blockScalarLevi_of_abs T (D j) _ (fun _ => e)
      (fun l => by
        rw [testScalars_full]
        exact LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T e)]
    simp
  · intro i _ hi
    rw [testScalars_of_ne T C D j _ e hi, map_one, map_one]
  · intro h
    exact absurd (Finset.mem_univ j) h

end Langlands.ProductLeviNecessity
