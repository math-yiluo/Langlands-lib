import Langlands.Representation.RankinSelberg.EqualRankSliceSupportStatement
import Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof
import Langlands.Representation.Conductor.SphericalIntegrals
import Langlands.LocalField.Normalization.Continuity

/-!
# Proof of equal-rank determinant-slice lower support

On every sufficiently negative determinant slice the equal-rank integrand vanishes
pointwise, so its Bochner integral is zero. The bound combines the published uniform
simple-root support of smooth Whittaker coefficients, the Iwasawa decomposition and
the compact support of the row test function. No convergence is used.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Ultrametric bound for a finite sum of the normalized absolute value. -/
theorem normalizedAbs_finsetSum_le {ι : Type*} (s : Finset ι) (x : ι → F.Carrier) {C : ℝ}
    (hC : 0 ≤ C) (hx : ∀ i ∈ s, T.normalizedAbs (x i) ≤ C) :
    T.normalizedAbs (∑ i ∈ s, x i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [T.normalizedAbs_zero] using hC
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (T.normalizedAbs_add_le_max _ _).trans
      (max_le (hx i (Finset.mem_insert_self i s))
        (ih fun j hj => hx j (Finset.mem_insert_of_mem hj)))

/-- A row Schwartz–Bruhat function vanishes outside a box `|x_j| ≤ C` for the
normalized absolute value. -/
theorem exists_schwartzBruhat_row_bound (n : ℕ) :
    letI := T.topology
    ∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Fin (n + 1) → F.Carrier, Φ x ≠ 0 → ∀ j, T.normalizedAbs (x j) ≤ C := by
  let := T.topology
  intro Φ
  have hc : Continuous fun x : Fin (n + 1) → F.Carrier => ∑ j, T.normalizedAbs (x j) :=
    continuous_finsetSum _ fun j _ => T.continuous_normalizedAbs.comp (continuous_apply j)
  obtain ⟨C, hC⟩ :=
    (SchwartzBruhat.hasCompactSupport Φ).isCompact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx j => ?_⟩
  have hb := hC x (subset_tsupport _ hx)
  rw [Real.norm_eq_abs] at hb
  calc T.normalizedAbs (x j) ≤ ∑ j, T.normalizedAbs (x j) :=
        Finset.single_le_sum (fun j _ => T.normalizedAbs_nonneg (x j)) (Finset.mem_univ j)
    _ ≤ |∑ j, T.normalizedAbs (x j)| := le_abs_self _
    _ ≤ C := hb
    _ ≤ max C 0 := le_max_left _ _

/-- Determinant bound at a nonvanishing point. If the adjacent diagonal ratios of the
Iwasawa diagonal are bounded by `R` wherever `W` is nonzero, and the last row of `g`
lies in the box `|x_j| ≤ C`, then `|det g| ≤ ∏_i R^(n-i) C`. -/
theorem normalizedAbs_determinant_le_of_simpleRoot (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (W : WhittakerFunctions ψ n) {R C : ℝ},
      0 < R → 0 ≤ C →
      (∀ (a : Fin (n + 1) → F.Carrierˣ) (κ : Langlands.GeneralLinear (n + 1) F.Carrier),
        κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
        W.val (Iwasawa.diagonalUnits a * κ) ≠ 0 →
        ∀ i : Fin n,
          T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) ≤ R) →
      ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier, W.val g ≠ 0 →
        (∀ j, T.normalizedAbs (lastRow g j) ≤ C) →
        T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) ≤
          ∏ i : Fin (n + 1), R ^ (n - i.val) * C := by
  let := T.topology
  let := T.valuativeRel
  intro ψ W R C hR hC hroot g hW hrow
  obtain ⟨b, hb, k, hk, rfl⟩ :=
    Iwasawa.exists_upperTriangular_mul (ValuativeRel.valuation F.Carrier) g
  have hd : ∀ i, b i i ≠ 0 := by
    intro i h0
    apply Matrix.GeneralLinearGroup.det_ne_zero b
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  set a : Fin (n + 1) → F.Carrierˣ := fun i => Units.mk0 (b i i) (hd i) with ha
  set D := Iwasawa.diagonalUnits a with hD
  set u := b * D⁻¹ with hu
  have hval : u.val = b.val * Matrix.diagonal fun i => (b i i)⁻¹ := by
    rw [hu, Units.val_mul, hD, ← map_inv, Iwasawa.diagonalUnits_val]
    congr 1
  have humem : u ∈ upperUnipotent (n + 1) F.Carrier := by
    refine ⟨?_, fun i => ?_⟩
    · rw [hval]
      exact hb.mul (Matrix.blockTriangular_diagonal _)
    · change u.val i i = 1
      rw [hval, Matrix.mul_diagonal, mul_inv_cancel₀ (hd i)]
  have hg : b * k = u * (D * k) := by
    rw [hu, mul_assoc, inv_mul_cancel_left]
  rw [hg] at hW hrow ⊢
  -- Simple-root bounds at the point `D k`.
  have hWD : W.val (D * k) ≠ 0 := by
    intro h
    apply hW
    have h1 : W.val (u * (D * k)) = _ := W.property ⟨u, humem⟩ (D * k)
    rw [h1, h, mul_zero]
  have hratio := hroot a k hk hWD
  -- The last diagonal entry is bounded through the last row.
  have hrow' : ∀ j, T.normalizedAbs (lastRow (D * k) j) ≤ C := by
    have h1 : lastRow (u * (D * k)) = lastRow (D * k) :=
      lastRow_unipotent_mul ⟨u, humem⟩ (D * k)
    rw [← h1]
    exact hrow
  have hkmem := (Conductor.mem_integralSubgroup _ n k).1 hk
  have hlast : ((a (Fin.last n) : F.Carrierˣ) : F.Carrier) =
      ∑ j, lastRow (D * k) j * (k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) j
        (Fin.last n) := by
    have h : (D * k).val * (k⁻¹).val = D.val := by
      rw [← Units.val_mul, mul_inv_cancel_right]
    have h2 := congrFun (congrFun h (Fin.last n)) (Fin.last n)
    rw [Matrix.mul_apply, hD, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq] at h2
    exact h2.symm
  have hlastle : T.normalizedAbs ((a (Fin.last n) : F.Carrierˣ) : F.Carrier) ≤ C := by
    rw [hlast]
    refine normalizedAbs_finsetSum_le T _ _ hC fun j _ => ?_
    rw [T.normalizedAbs_mul]
    have hk1 : T.normalizedAbs
        ((k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) j (Fin.last n)) ≤ 1 :=
      (T.normalizedAbs_le_one_iff_mem_integers _).2 (hkmem.2 j (Fin.last n))
    calc T.normalizedAbs (lastRow (D * k) j) *
          T.normalizedAbs ((k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier) j (Fin.last n))
        ≤ C * 1 := mul_le_mul (hrow' j) hk1 (T.normalizedAbs_nonneg _) hC
      _ = C := mul_one C
  -- Reverse induction along the diagonal.
  have hdiag : ∀ i : Fin (n + 1),
      T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) ≤ R ^ (n - i.val) * C := by
    intro i
    induction i using Fin.reverseInduction with
    | last => simpa using hlastle
    | cast i ih =>
      have hsplit : ((a i.castSucc : F.Carrierˣ) : F.Carrier) =
          ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) *
            ((a i.succ : F.Carrierˣ) : F.Carrier) := by
        rw [← Units.val_mul, div_mul_cancel]
      have hexp : n - i.castSucc.val = (n - i.succ.val) + 1 := by
        rw [Fin.val_castSucc, Fin.val_succ]
        omega
      rw [hsplit, T.normalizedAbs_mul, hexp, pow_succ', mul_assoc]
      exact mul_le_mul (hratio i) ih (T.normalizedAbs_nonneg _) hR.le
  -- The determinant.
  have hdetk : T.normalizedAbs (Matrix.det k.val) ≤ 1 := by
    have hv := Conductor.valuation_det_of_mem_integralSubgroup hk
    exact (T.normalizedAbs_le_one_iff_mem_integers _).2
      ((Valuation.mem_integer_iff _ _).2 hv.le)
  have hdet : (GeneralLinear.determinant (u * (D * k)) : F.Carrier) =
      (∏ i, ((a i : F.Carrierˣ) : F.Carrier)) * Matrix.det k.val := by
    have h1 : GeneralLinear.determinant (u * (D * k)) = GeneralLinear.determinant (D * k) :=
      determinant_unipotent_mul ⟨u, humem⟩ (D * k)
    rw [h1]
    change Matrix.det (D.val * k.val) = _
    rw [Matrix.det_mul, hD, Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
  have hprod : T.normalizedAbs (∏ i, ((a i : F.Carrierˣ) : F.Carrier)) =
      ∏ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) := by
    rw [← normalizedAbsoluteValue_apply, map_prod]
    rfl
  rw [hdet, T.normalizedAbs_mul, hprod]
  calc (∏ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier)) *
        T.normalizedAbs (Matrix.det k.val)
      ≤ (∏ i : Fin (n + 1), R ^ (n - i.val) * C) * 1 :=
        mul_le_mul
          (Finset.prod_le_prod₀ (fun i _ => T.normalizedAbs_nonneg _) fun i _ => hdiag i)
          hdetk (T.normalizedAbs_nonneg _)
          (Finset.prod_nonneg fun i _ => mul_nonneg (pow_nonneg hR.le _) hC)
    _ = ∏ i : Fin (n + 1), R ^ (n - i.val) * C := mul_one _

/-- JPSS (1983), Section 4.2, printed page 407: the equal-rank slice coefficients have
support bounded below, for all data of the statement. -/
theorem equalRankSliceSupport {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankSliceSupportStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ _ μ _ V _ _ W _ _ π σ hπ _ ℓ ℓ' f f' Φ
  obtain ⟨R, hR, hroot⟩ := Whittaker.smoothSimpleRootSupport.{uF, uV} F T n ψ V π hπ.1.1 ℓ f
  obtain ⟨C, hC, hΦ⟩ := exists_schwartzBruhat_row_bound T n Φ
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∏ i : Fin (n + 1), R ^ (n - i.val) * C) hq
  refine (BilateralLaurentSeries.hasLowerBoundedSupport_iff
    (equalRankSliceCoefficient T μ ψ f.val f'.val Φ)).2 ⟨-(N : ℤ), fun m hm => ?_⟩
  rw [equalRankSliceCoefficient_def T μ ψ f.val f'.val Φ m]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  induction x using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hx
    rw [equalRankIntegrand_zero_mk]
    by_contra hne
    have hW : f.val.val g ≠ 0 := fun h => hne (by rw [h, zero_mul, zero_mul])
    have hP : Φ (lastRow g) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hdet := normalizedAbs_determinant_le_of_simpleRoot T n ψ f.val hR hC hroot g hW
      (hΦ _ hP)
    rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant g).ne_zero, hx] at hdet
    have hle : (T.residueCardinality : ℝ) ^ (N : ℤ) ≤ (T.residueCardinality : ℝ) ^ (-m) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    rw [zpow_natCast] at hle
    linarith

end Langlands.RankinSelberg
