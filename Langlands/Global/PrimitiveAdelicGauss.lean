import Langlands.Global.PrimitiveAdelicBounded
import Langlands.Global.MixedSpaceDirichlet
import Langlands.Global.AdeleQuotientCompactProof

/-! # A rank-two height bound for actual primitive adelic vectors -/

noncomputable section

universe u

open scoped NNReal Topology Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

open NumberField

variable (F : Type u) [Field F] [NumberField F]

/-- The vector `(x l + u m, m)`, the image of the rational vector `(l, m)` under the
upper triangular adelic matrix with rows `(x, u)` and `(0, 1)`. -/
def rankTwoVector (x : Ideles F) (u : Adeles F) (l m : F) : Vector F 2 :=
  ![x.val * diagonal F l + u * diagonal F m, diagonal F m]

theorem rankTwoVector_eq_mulVec (x : Ideles F) (u : Adeles F) (l m : F) :
    rankTwoVector F x u l m = !![x.val, u; 0, 1] *ᵥ rational F 2 ![l, m] := by
  funext i
  fin_cases i <;> simp [rankTwoVector, rational, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {F} in
theorem norm_le_one_of_mem {v : FinitePlace F} {a : FiniteCompletion F v}
    (ha : a ∈ v.adicCompletionIntegers F) : ‖a‖ ≤ 1 := by
  simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← Valued.toNormedField.norm_le_one_iff] using ha

theorem finiteProjection_integer_mem (v : FinitePlace F) (d : 𝓞 F) :
    finiteProjection F v (diagonal F (d : F)) ∈ v.adicCompletionIntegers F := by
  rw [finiteProjection_diagonal]
  exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v d

/-- A compact set of finite adeles has a common nonzero integral denominator. -/
theorem exists_denominator_of_isCompact {K : Set (FiniteAdeles F)} (hK : IsCompact K) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K, ∀ v : FinitePlace F,
      algebraMap (𝓞 F) (FiniteCompletion F v) d * a v ∈ v.adicCompletionIntegers F := by
  classical
  have hmem (d : 𝓞 F) (a : FiniteAdeles F) (v : FinitePlace F) :
      (algebraMap (𝓞 F) (FiniteAdeles F) d * a) v =
        algebraMap (𝓞 F) (FiniteCompletion F v) d * a v := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F),
      IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteCompletion F v)]
    rfl
  let U : {d : 𝓞 F // d ≠ 0} → Set (FiniteAdeles F) := fun d =>
    (fun a => algebraMap (𝓞 F) (FiniteAdeles F) d.1 * a) ⁻¹'
      (integralFiniteAdeles F : Set (FiniteAdeles F))
  have hU (d : {d : 𝓞 F // d ≠ 0}) : IsOpen (U d) :=
    (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul continuous_id)
  have hcov : K ⊆ ⋃ d, U d := by
    intro a _
    obtain ⟨d, hd, h⟩ := exists_integer_mul_mem_adicCompletionIntegers a
    refine Set.mem_iUnion.mpr ⟨⟨d, hd⟩, (mem_integralFiniteAdeles F _).mpr fun v => ?_⟩
    rw [hmem]
    exact h v
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  refine ⟨∏ d ∈ t, d.1, Finset.prod_ne_zero_iff.mpr fun d _ => d.2, fun a ha v => ?_⟩
  obtain ⟨d, hdt, hd⟩ := Set.mem_iUnion₂.mp (ht ha)
  have h := (mem_integralFiniteAdeles F _).mp hd v
  rw [hmem] at h
  rw [← Finset.mul_prod_erase t (fun d => d.1) hdt, map_mul,
    mul_comm (algebraMap _ _ d.1), mul_assoc]
  exact mul_mem (IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v _) h

/-- The archimedean components of a compact set of ideles are uniformly bounded. -/
theorem exists_infinite_bound_of_isCompact {C : Set (Ideles F)} (hC : IsCompact C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ C, ∀ w : InfinitePlace F,
      ‖infiniteProjection F w c.val‖ ≤ A := by
  have hcont : Continuous fun c : Ideles F =>
      ∑ w : InfinitePlace F, ‖infiniteProjection F w c.val‖ :=
    continuous_finsetSum _ fun w _ =>
      ((continuous_infiniteProjection F w).comp Units.continuous_val).norm
  obtain ⟨A, hA⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max A 0, le_max_right _ _, fun c hc w => ?_⟩
  calc ‖infiniteProjection F w c.val‖
      ≤ ∑ w' : InfinitePlace F, ‖infiniteProjection F w' c.val‖ :=
        Finset.single_le_sum (f := fun w' => ‖infiniteProjection F w' c.val‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
    _ ≤ ‖∑ w' : InfinitePlace F, ‖infiniteProjection F w' c.val‖‖ := Real.le_norm_self _
    _ ≤ A := hA c hc
    _ ≤ max A 0 := le_max_left _ _

/-- Local bounds give the height bound with the archimedean multiplicities. -/
theorem height_le_pow_of_local_le {n : ℕ} (x : Vector F n) {M : ℝ} (hM : 0 ≤ M)
    (hfin : ∀ v, finiteNorm F n x v ≤ 1) (hinf : ∀ w, infiniteNorm F n x w ≤ M) :
    height F n x ≤ M ^ Module.finrank ℚ F := by
  have hprod : ∏ w : InfinitePlace F, infiniteNorm F n x w ^ w.mult ≤
      M ^ Module.finrank ℚ F := by
    calc ∏ w : InfinitePlace F, infiniteNorm F n x w ^ w.mult
        ≤ ∏ w : InfinitePlace F, M ^ w.mult :=
          Finset.prod_le_prod₀ (fun w _ => pow_nonneg (norm_nonneg _) _)
            (fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hinf w) _)
      _ = M ^ Module.finrank ℚ F := by
          rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  have hfp : ∏ᶠ v, finiteNorm F n x v ≤ 1 := by
    by_cases hs : (Function.mulSupport (finiteNorm F n x)).Finite
    · rw [finprod_eq_prod _ hs]
      exact Finset.prod_le_one₀ (fun v _ => norm_nonneg _) (fun v _ => hfin v)
    · rw [finprod_of_infinite_mulSupport hs]
  calc height F n x ≤ M ^ Module.finrank ℚ F * 1 :=
        mul_le_mul hprod hfp (finprod_nonneg fun v => norm_nonneg _) (pow_nonneg hM _)
    _ = M ^ Module.finrank ℚ F := mul_one _

theorem norm_first_eq_one {K : Type*} [NormedField K] :
    ‖(![1, 0] : Fin 2 → K)‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![1, 0] : Fin 2 → K) 0

/-- The first standard rational vector has height one. -/
theorem height_rational_first : height F 2 (rational F 2 ![1, 0]) = 1 := by
  have hfin (v : FinitePlace F) : finiteNorm F 2 (rational F 2 ![1, 0]) v = 1 := by
    have h : (fun i : Fin 2 => finiteProjection F v (rational F 2 ![1, 0] i)) = ![1, 0] := by
      funext i
      fin_cases i <;> simp [rational]
    rw [finiteNorm, h, norm_first_eq_one]
  have hinf (w : InfinitePlace F) : infiniteNorm F 2 (rational F 2 ![1, 0]) w = 1 := by
    have h : (fun i : Fin 2 => infiniteProjection F w (rational F 2 ![1, 0] i)) = ![1, 0] := by
      funext i
      fin_cases i <;> simp [rational]
    rw [infiniteNorm, h, norm_first_eq_one]
  simp only [height, hfin, hinf, one_pow, Finset.prod_const_one, finprod_one, mul_one]

/-- With coefficients `(1, 0)` the height is the normalized absolute value of `x`. -/
theorem height_rankTwoVector_one_zero (x : Ideles F) (u : Adeles F) :
    height F 2 (rankTwoVector F x u 1 0) = ((IdeleAbsoluteValue.full F x : ℝ≥0) : ℝ) := by
  have he : IsPrimitive F 2 (rational F 2 ![1, 0]) :=
    ⟨1, ![1, 0], by simp, by simp⟩
  have hv : rankTwoVector F x u 1 0 = x.val • rational F 2 ![1, 0] := by
    funext i
    fin_cases i <;> simp [rankTwoVector, rational]
  rw [hv, he.height_smul F 2, height_rational_first, mul_one]

/-- **Rank-two height bound.** There is a constant `C` such that for every idele `x`
and adele `u` some nonzero rational vector `(l, m)` has image of height at most
`C √|x|` under the adelic matrix with rows `(x, u)` and `(0, 1)`. -/
theorem exists_rankTwoVector_height_le :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ (x : Ideles F) (u : Adeles F), ∃ l m : F, (l ≠ 0 ∨ m ≠ 0) ∧
      height F 2 (rankTwoVector F x u l m) ≤
        Cst * Real.sqrt ((IdeleAbsoluteValue.full F x : ℝ≥0) : ℝ) := by
  classical
  obtain ⟨C, hC, -, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  obtain ⟨A, hA0, hA⟩ := exists_infinite_bound_of_isCompact F hC
  obtain ⟨D, hD0, hD⟩ := exists_denominator_of_isCompact F
    (hC.image (continuous_snd.comp Units.continuous_val))
  let E : ℝ := ∑ w : InfinitePlace F, ‖infiniteProjection F w (diagonal F (D : F))‖
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun w _ => norm_nonneg _
  have hE (w : InfinitePlace F) : ‖infiniteProjection F w (diagonal F (D : F))‖ ≤ E :=
    Finset.single_le_sum (f := fun w' => ‖infiniteProjection F w' (diagonal F (D : F))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  let B : ℝ := MixedSpaceDirichlet.basisBound F
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
  let K : ℝ := E * B * (A + 2)
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hE0 hB0) (by linarith)
  refine ⟨max (K ^ Module.finrank ℚ F) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun x u => ?_⟩
  set H : ℝ := ((IdeleAbsoluteValue.full F x : ℝ≥0) : ℝ) with hH
  have hH0 : 0 ≤ H := NNReal.coe_nonneg _
  by_cases hsmall : H ≤ 1
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    rw [height_rankTwoVector_one_zero]
    calc H = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt hH0).symm
      _ ≤ 1 * Real.sqrt H :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr hsmall) (Real.sqrt_nonneg _)
      _ ≤ max (K ^ Module.finrank ℚ F) 1 * Real.sqrt H :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  push Not at hsmall
  let h : ℝ≥0ˣ := IdeleAbsoluteValue.full F x
  let r : ℝ≥0ˣ := scalarRoot F h
  let R : ℝ := ((r : ℝ≥0) : ℝ)
  have hRpow : R ^ Module.finrank ℚ F = H :=
    congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) (scalarRoot_pow F h)
  have hR0 : 0 < R := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr r.ne_zero)
  have hR1 : 1 ≤ R := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_one₀ hR0.le hlt (Module.finrank_pos (R := ℚ) (M := F)).ne'
    linarith
  let s : Ideles F := PositiveRealIdeles.full F r
  have hs : IdeleAbsoluteValue.full F s = h := absoluteValue_scalarRoot F h
  have hz : s⁻¹ * x ∈ NormOneIdeleClass.normOneIdeles F := by
    change IdeleAbsoluteValue.full F (s⁻¹ * x) = 1
    rw [map_mul, map_inv, hs, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hcover (s⁻¹ * x) hz
  set c : Ideles F := diagonalUnits F a * (s⁻¹ * x) with hc
  let t : Ideles F := s * c
  have hxt : x.val * diagonal F (a : F) = t.val := by
    have ht : t = diagonalUnits F a * x := by
      change s * (diagonalUnits F a * (s⁻¹ * x)) = diagonalUnits F a * x
      rw [mul_left_comm s, mul_inv_cancel_left]
    rw [ht, Units.val_mul, mul_comm]
    rfl
  let z : Adeles F := u * (t⁻¹).val
  have hu : u = z * t.val := by
    change u = u * (t⁻¹).val * t.val
    rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  obtain ⟨q, hq⟩ := exists_sub_mem_integralFiniteAdeles z.2
  let y : Adeles F := z - diagonal F q
  let N : ℕ := ⌈Real.sqrt R⌉₊
  have hsq1 : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR1
  have hN : 0 < N := Nat.ceil_pos.mpr (by linarith)
  have hNge : Real.sqrt R ≤ N := Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 2 * Real.sqrt R := by
    have := Nat.ceil_lt_add_one (Real.sqrt_nonneg R)
    linarith
  obtain ⟨l0, m0, hm0, hb⟩ := MixedSpaceDirichlet.exists_dirichlet_infiniteAdeles F y.1 N hN
  refine ⟨(a : F) * ((D : F) * ((l0 : F) - (m0 : F) * q)), (D : F) * (m0 : F),
    Or.inr (mul_ne_zero (by exact_mod_cast hD0) (by exact_mod_cast hm0)), ?_⟩
  have hV : rankTwoVector F x u ((a : F) * ((D : F) * ((l0 : F) - (m0 : F) * q)))
      ((D : F) * (m0 : F)) =
      ![t.val * (diagonal F (D : F) * (diagonal F (l0 : F) + diagonal F (m0 : F) * y)),
        diagonal F (D : F) * diagonal F (m0 : F)] := by
    funext i
    fin_cases i
    · simp only [rankTwoVector, y, map_mul, map_sub]
      simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [hu, ← hxt]
      ring
    · simp [rankTwoVector]
  rw [hV]
  have hfin (v : FinitePlace F) : finiteNorm F 2
      ![t.val * (diagonal F (D : F) * (diagonal F (l0 : F) + diagonal F (m0 : F) * y)),
        diagonal F (D : F) * diagonal F (m0 : F)] v ≤ 1 := by
    have hDc : finiteProjection F v (diagonal F (D : F)) * finiteProjection F v c.val ∈
        v.adicCompletionIntegers F := by
      have h := hD c.val.2 ⟨c, ha, rfl⟩ v
      rwa [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteCompletion F v)] at h
    have hy : finiteProjection F v y ∈ v.adicCompletionIntegers F :=
      (mem_integralFiniteAdeles F _).mp hq v
    have hts : finiteProjection F v t.val = finiteProjection F v c.val := by
      change finiteProjection F v (s.val * c.val) = _
      rw [map_mul]
      change (PositiveRealIdeles.full F r).val.2 v * _ = _
      rw [PositiveRealIdeles.full_finite_value, one_mul]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show ‖finiteProjection F v (t.val * (diagonal F (D : F) *
        (diagonal F (l0 : F) + diagonal F (m0 : F) * y)))‖ ≤ 1
      apply norm_le_one_of_mem
      rw [map_mul, map_mul, map_add, map_mul, hts, ← mul_assoc,
        mul_comm (finiteProjection F v c.val)]
      exact mul_mem hDc (add_mem (finiteProjection_integer_mem F v l0)
        (mul_mem (finiteProjection_integer_mem F v m0) hy))
    · show ‖finiteProjection F v (diagonal F (D : F) * diagonal F (m0 : F))‖ ≤ 1
      apply norm_le_one_of_mem
      rw [map_mul]
      exact mul_mem (finiteProjection_integer_mem F v D) (finiteProjection_integer_mem F v m0)
  have hsR := Real.sqrt_nonneg R
  have hinf (w : InfinitePlace F) : infiniteNorm F 2
      ![t.val * (diagonal F (D : F) * (diagonal F (l0 : F) + diagonal F (m0 : F) * y)),
        diagonal F (D : F) * diagonal F (m0 : F)] w ≤ K * Real.sqrt R := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK0 hsR)).mpr
      (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show ‖infiniteProjection F w (t.val * (diagonal F (D : F) *
        (diagonal F (l0 : F) + diagonal F (m0 : F) * y)))‖ ≤ K * Real.sqrt R
      have hts : ‖infiniteProjection F w t.val‖ ≤ R * A := by
        change ‖infiniteProjection F w (s.val * c.val)‖ ≤ R * A
        rw [map_mul, norm_mul]
        have h1 : ‖infiniteProjection F w s.val‖ = R :=
          PositiveRealIdeles.norm_full_infinite_value F w r
        rw [h1]
        exact mul_le_mul_of_nonneg_left (hA c ha w) hR0.le
      have hl : ‖infiniteProjection F w (diagonal F (l0 : F) + diagonal F (m0 : F) * y)‖ ≤
          B / N := (hb w).2
      have hRN : R / N ≤ Real.sqrt R :=
        (div_le_div_of_nonneg_left hR0.le (by linarith) hNge).trans_eq Real.div_sqrt
      rw [map_mul, map_mul, norm_mul, norm_mul]
      calc ‖infiniteProjection F w t.val‖ *
            (‖infiniteProjection F w (diagonal F (D : F))‖ *
              ‖infiniteProjection F w (diagonal F (l0 : F) + diagonal F (m0 : F) * y)‖)
          ≤ (R * A) * (E * (B / N)) :=
            mul_le_mul hts (mul_le_mul (hE w) hl (norm_nonneg _) hE0)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hR0.le hA0)
        _ = A * E * B * (R / N) := by ring
        _ ≤ A * E * B * Real.sqrt R :=
            mul_le_mul_of_nonneg_left hRN (mul_nonneg (mul_nonneg hA0 hE0) hB0)
        _ ≤ K * Real.sqrt R := by
            have : K * Real.sqrt R = A * E * B * Real.sqrt R + 2 * (E * B * Real.sqrt R) := by
              simp only [K]
              ring
            rw [this]
            have := mul_nonneg (mul_nonneg hE0 hB0) hsR
            linarith
    · show ‖infiniteProjection F w (diagonal F (D : F) * diagonal F (m0 : F))‖ ≤
        K * Real.sqrt R
      rw [map_mul, norm_mul]
      calc ‖infiniteProjection F w (diagonal F (D : F))‖ *
            ‖infiniteProjection F w (diagonal F (m0 : F))‖
          ≤ E * (N * B) := mul_le_mul (hE w) (hb w).1 (norm_nonneg _) hE0
        _ ≤ E * ((2 * Real.sqrt R) * B) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNle hB0) hE0
        _ ≤ K * Real.sqrt R := by
            have : K * Real.sqrt R = E * ((2 * Real.sqrt R) * B) +
                A * (E * B * Real.sqrt R) := by
              simp only [K]
              ring
            rw [this]
            have := mul_nonneg hA0 (mul_nonneg (mul_nonneg hE0 hB0) hsR)
            linarith
  have hsqrt : Real.sqrt R ^ Module.finrank ℚ F = Real.sqrt H := by
    rw [← hRpow]
    symm
    rw [Real.sqrt_eq_iff_eq_sq (pow_nonneg hR0.le _) (pow_nonneg hsR _), ← pow_mul,
      mul_comm, pow_mul, Real.sq_sqrt hR0.le]
  calc height F 2 _ ≤ (K * Real.sqrt R) ^ Module.finrank ℚ F :=
        height_le_pow_of_local_le F _ (mul_nonneg hK0 hsR) hfin hinf
    _ = K ^ Module.finrank ℚ F * Real.sqrt H := by rw [mul_pow, hsqrt]
    _ ≤ max (K ^ Module.finrank ℚ F) 1 * Real.sqrt H :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

end Langlands.Global.PrimitiveAdelicHeight
