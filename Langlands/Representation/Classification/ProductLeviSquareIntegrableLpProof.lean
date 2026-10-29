import Langlands.Representation.Classification.ProductLeviSquareIntegrableLpStatement
import Langlands.Representation.Classification.ProductLeviStrictChamberBound

/-!
# Discrete-series coefficients of block Levis below exponent two

Proof of `GLProductLeviSquareIntegrableLpStatement`. Square integrability gives
the strict exponent bound at the fundamental coweights, the strict exponent bound
gives a chamber bound `c ∏ j, δ(lam_j) ^ (1/2 + ε)`, and the Cartan cell volumes
`≤ c' ∏ j, δ(lam_j)⁻¹` turn it into `L^r` integrability for
`r = 2 (1 + ε) / (1 + 2 ε) < 2`.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace Langlands.ProductLeviSquareIntegrable

open GeneralLinear Geometric ProductLeviChamber ProductLeviTempered

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An admissible representation satisfying the strict exponent hypothesis has
every absolute matrix coefficient in `L^r` of the central quotient for some
`1 < r < 2`, given the Cartan coset count. -/
theorem memLp_of_strict (hcount : CartanQuotient.CartanCellCountStatement.{uF}) :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (ρ : Representation ℂ (C.Levi F.Carrier) V),
      IsAdmissible ρ → StrictFundHypothesis T C ρ →
      ∀ (c : UnitaryCentralCharacter ρ) (ℓ : SmoothDual ρ) (v : V),
        ∃ r : ℝ, 1 < r ∧ r < 2 ∧
          MeasureTheory.MemLp (c.coefficientNorm (ℓ : Module.Dual ℂ V) v)
            (ENNReal.ofReal r) μ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ ρ hadm hstrict c ℓ v
  classical
  obtain ⟨ε, hε, cb, hcb⟩ := strict_cell_coefficient_bound T C ρ hadm hstrict ℓ v
  obtain ⟨cc, hcc0, hcc⟩ := measure_cellQ_le T C hcount
  have hd : (0 : ℝ) < 1 + 2 * ε := by positivity
  let P : ℝ := 2 * (1 + ε) / (1 + 2 * ε)
  have hP1 : 1 < P := by
    rw [lt_div_iff₀ hd]
    linarith
  have hP2 : P < 2 := by
    rw [div_lt_iff₀ hd]
    linarith
  have hP : 0 < P := by linarith
  refine ⟨P, hP1, hP2, ?_⟩
  let w : FundIndex C → ℝ := fun s => fundWeight T C s
  have hw0 : ∀ s, 0 < w s := fun s => fundWeight_pos T C s
  have hw1 : ∀ s, w s < 1 := fun s => fundWeight_lt_one T C s
  let y : FundIndex C → ℝ := fun s => w s ^ ((1 : ℝ) / 2 + ε)
  have hy0 : ∀ s, 0 ≤ y s := fun s => Real.rpow_nonneg (hw0 s).le _
  let x : FundIndex C → ℝ := fun s => y s ^ P * (w s)⁻¹
  have hx0 : ∀ s, 0 ≤ x s := fun s =>
    mul_nonneg (Real.rpow_nonneg (hy0 s) _) (inv_nonneg.mpr (hw0 s).le)
  have hx1 : ∀ s, x s < 1 := by
    intro s
    have hκ : ((1 : ℝ) / 2 + ε) * P + -1 = ε := by
      simp only [P]
      field_simp
      ring
    have hxs : x s = w s ^ (((1 : ℝ) / 2 + ε) * P + -1) := by
      simp only [x, y]
      rw [Real.rpow_add (hw0 s) (((1 : ℝ) / 2 + ε) * P) (-1), Real.rpow_mul (hw0 s).le,
        Real.rpow_neg_one]
    rw [hxs, hκ]
    exact Real.rpow_lt_one (hw0 s).le (hw1 s) hε
  let b : (FundIndex C → ℕ) → ℝ≥0∞ := fun m => ENNReal.ofReal (|cb| * ∏ s, y s ^ m s)
  let S0 : Set (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)) :=
    QuotientGroup.mk '' (integralLevi T C : Set (C.Levi F.Carrier))
  have hS0 : μ S0 < ⊤ := measure_image_integralLevi_lt_top T C μ
  have hp0 : ENNReal.ofReal P ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hP
  have hmeas := c.aestronglyMeasurable_coefficientNorm (ℓ : Module.Dual ℂ V) v (hadm.1 v) μ
  have hcover : (⋃ m, cellQ T C (latticeTuple C m)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨lam, hlam, k₁, hk₁, k₂, hk₂, hq⟩ := exists_cell T C g
    refine Set.mem_iUnion.mpr ⟨fundCoeff C lam, k₁, hk₁, k₂, hk₂, ?_⟩
    rw [latticeTuple_fundCoeff C lam hlam]
    exact hq
  have hbound : ∀ m q, q ∈ cellQ T C (latticeTuple C m) →
      ‖c.coefficientNorm (ℓ : Module.Dual ℂ V) v q‖ₑ ≤ b m := by
    rintro m q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    rw [Real.enorm_of_nonneg (c.coefficientNorm_nonneg _ _ _),
      UnitaryCentralCharacter.coefficientNorm_mk]
    apply ENNReal.ofReal_le_ofReal
    have h := hcb (latticeTuple C m) (latticeTuple_normalized C m) k₁ hk₁ k₂ hk₂
    have hprod : ∏ j, CartanQuotient.delta T (latticeTuple C m j) ^ ((1 : ℝ) / 2 + ε) =
        ∏ s, y s ^ m s := by
      rw [Real.finsetProd_rpow _ _ (fun j _ => (CartanQuotient.delta_pos T _).le),
        prod_delta_latticeTuple, ← Real.finsetProd_rpow _ _
          (fun s _ => pow_nonneg (fundWeight_pos T C s).le _)]
      apply Finset.prod_congr rfl
      intro s _
      exact (Real.rpow_pow_comm (fundWeight_pos T C s).le _ _).symm
    rw [hprod] at h
    calc _ ≤ cb * ∏ s, y s ^ m s := h
      _ ≤ |cb| * ∏ s, y s ^ m s :=
        mul_le_mul_of_nonneg_right (le_abs_self _)
          (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _)
  have halg : ∀ m : FundIndex C → ℕ,
      (|cb| * ∏ s, y s ^ m s) ^ P *
          ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹ =
        (|cb| ^ P * ∏ j, cc j) * ∏ s, x s ^ m s := by
    intro m
    rw [Real.mul_rpow (abs_nonneg _) (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _),
      ← Real.finsetProd_rpow _ _ (fun s _ => pow_nonneg (hy0 s) _), Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, prod_delta_latticeTuple, ← Finset.prod_inv_distrib]
    have h1 : ∏ s, (y s ^ m s) ^ P = ∏ s, (y s ^ P) ^ m s :=
      Finset.prod_congr rfl fun s _ => (Real.rpow_pow_comm (hy0 s) _ _).symm
    have h2 : ∏ s, x s ^ m s = (∏ s, (y s ^ P) ^ m s) * ∏ s, (fundWeight T C s ^ m s)⁻¹ := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro s _
      simp only [x, w]
      rw [mul_pow, inv_pow]
    rw [h1, h2]
    ring
  have hterm : ∀ m : FundIndex C → ℕ,
      b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m)) ≤
        (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) * ENNReal.ofReal (∏ s, x s ^ m s) := by
    intro m
    rw [ENNReal.toReal_ofReal hP.le]
    have hμ := hcc μ (latticeTuple C m) (fun j => (latticeTuple_normalized C m j).1)
    have hnn1 : 0 ≤ |cb| * ∏ s, y s ^ m s :=
      mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun s _ => pow_nonneg (hy0 s) _)
    have hnn2 : 0 ≤ ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹ :=
      Finset.prod_nonneg fun j _ =>
        mul_nonneg (hcc0 j) (inv_nonneg.mpr (CartanQuotient.delta_pos T _).le)
    calc b m ^ P * μ (cellQ T C (latticeTuple C m))
        ≤ b m ^ P * (ENNReal.ofReal
            (∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹) * μ S0) := by
          gcongr
      _ = ENNReal.ofReal ((|cb| * ∏ s, y s ^ m s) ^ P *
            ∏ j, cc j * (CartanQuotient.delta T (latticeTuple C m j))⁻¹) * μ S0 := by
          simp only [b]
          rw [ENNReal.ofReal_rpow_of_nonneg hnn1 hP.le, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hnn1 _)]
      _ = (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ENNReal.ofReal (∏ s, x s ^ m s) := by
          rw [halg, ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            (Finset.prod_nonneg fun j _ => hcc0 j))]
          ring
  have hlattice : (∑' m : FundIndex C → ℕ, ENNReal.ofReal (∏ s, x s ^ m s)) < ⊤ := by
    have h := finiteNatLatticeENNRealSummability (FundIndex C) x hx0 hx1 0 le_rfl
    simpa only [Real.rpow_eq_pow, Real.rpow_zero, one_mul] using h
  have hsum : (∑' m, b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m))) < ⊤ := by
    calc (∑' m, b m ^ (ENNReal.ofReal P).toReal * μ (cellQ T C (latticeTuple C m)))
        ≤ ∑' m : FundIndex C → ℕ, (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ENNReal.ofReal (∏ s, x s ^ m s) := ENNReal.tsum_le_tsum hterm
      _ = (ENNReal.ofReal (|cb| ^ P * ∏ j, cc j) * μ S0) *
            ∑' m : FundIndex C → ℕ, ENNReal.ofReal (∏ s, x s ^ m s) := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS0) hlattice
  exact countableCellLpUpper _ (FundIndex C → ℕ) μ _ (ENNReal.ofReal P) hp0 ENNReal.ofReal_ne_top
    hmeas (fun m => cellQ T C (latticeTuple C m)) hcover b hbound hsum

end Langlands.ProductLeviSquareIntegrable

namespace Langlands

universe uF uW

/-- Every absolute matrix coefficient of an irreducible representation of an
actual standard block Levi that is square integrable modulo the centre lies in
`L^r` of the central quotient for some `1 < r < 2`. -/
theorem glProductLeviSquareIntegrableLp :
    GLProductLeviSquareIntegrableLpStatement.{uF, uW} := by
  intro p _ F T
  let := T.topology
  intro n _ B
  let := T.leviTopologicalGroup B
  intro M Q _ _ μ _ W _ _ σ _ hsq c ℓ w
  exact ProductLeviSquareIntegrable.memLp_of_strict T B
    GeneralLinear.CartanQuotient.cartanCellCount μ σ hsq.1
    (ProductLeviSquareIntegrable.strictFundHypothesis_of_squareIntegrable T B μ σ hsq) c ℓ w

end Langlands
