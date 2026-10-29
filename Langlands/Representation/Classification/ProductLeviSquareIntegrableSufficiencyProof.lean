import Langlands.Representation.Classification.ProductLeviSquareIntegrableSufficiencyStatement
import Langlands.Representation.Classification.ProductLeviStrictChamberBound
import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyProof

/-!
# Product-Levi square-integrability from strict upper Jacquet exponent bounds

Proof of `GLProductLeviSquareIntegrableExponentSufficiencyStatement`. Every
generalized eigencharacter of a smooth representation has open kernel, so the
core hypothesis applies to every generalized eigencharacter at the fundamental
refinements. The fundamental scalars are monotone and not constant on their
block, so the hypothesis gives the strict fundamental bound
`StrictFundHypothesis`. The strict chamber bound then bounds every coefficient
on the Cartan cells by `c ∏ j, δ(lam_j) ^ (1/2 + ε)`, and the cell volumes
`≤ c' ∏ j, δ(lam_j)⁻¹` make the squared coefficient summable over the cells.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace Langlands

universe uF uV

namespace ProductLeviSquareIntegrable

section OpenKernel

variable {A : Type*} [Group A]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- On a vector fixed by `a`, the defect operator `π a - c` acts as the scalar `1 - c`. -/
theorem pow_sub_smul_apply_of_fixed (π : Representation ℂ A V) {a : A} {v : V}
    (hv : π a v = v) (c : ℂ) (k : ℕ) :
    ((π a - c • 1) ^ k) v = (1 - c) ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (π a - c • 1) v = (1 - c) • v := by
      simp [hv, sub_smul]
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, h1, smul_smul, pow_succ]

variable [TopologicalSpace A] [SeparatelyContinuousMul A]

/-- A generalized eigencharacter of a smooth representation has open kernel: it
is trivial on the open stabilizer of a nonzero vector of its character space. -/
theorem isOpen_ker_of_isSmooth_of_isGeneralizedEigencharacter (π : Representation ℂ A V)
    (hπ : IsSmooth π) {χ : A →* ℂˣ} (hχ : IsGeneralizedEigencharacter π χ) :
    IsOpen (χ.ker : Set A) := by
  obtain ⟨k, v, hv0, hv⟩ := (isGeneralizedEigencharacter_iff π χ).mp hχ
  obtain ⟨U, hU⟩ := hπ v
  refine Subgroup.isOpen_mono (H₁ := U.toSubgroup) (fun u hu => ?_) U.isOpen
  have hfix : π u v = v := hU ⟨u, hu⟩
  have h := hv u
  rw [pow_sub_smul_apply_of_fixed π hfix] at h
  have h1 : (1 - (χ u : ℂ)) ^ k = 0 := (smul_eq_zero.mp h).resolve_right hv0
  have h2 : (χ u : ℂ) = 1 := (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h1)).symm
  exact MonoidHom.mem_ker.mpr (Units.ext h2)

end OpenKernel

open GeneralLinear Geometric ProductLeviChamber ProductLeviTempered

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Generalized eigencharacters of the normalized refined Jacquet module of a
smooth representation, on flattened block scalars, have open kernels. -/
theorem isOpen_ker_of_isGeneralizedEigencharacter_refined :
    letI := T.topology
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V), IsSmooth ρ →
    ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D ρ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hρ D ψ hgen
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let z := (flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
    ((C.flatten D).blockScalarLevi F.Carrier)
  have hzcont : Continuous z := by
    have hb : Continuous ((C.flatten D).blockScalarLevi F.Carrier) :=
      continuous_pi fun j =>
        (GeneralLinear.scalarContinuous (n := (C.flatten D).size j)).continuous.comp
          (continuous_apply j)
    exact (flattenedLeviEquivContinuous F.Carrier C D).continuous.comp hb
  exact isOpen_ker_of_isSmooth_of_isGeneralizedEigencharacter _
    (isSmooth_comp z hzcont (T.isSmooth_normalizedRefinedJacquet C D hρ)) hgen

/-- The weak and strict upper exponent bounds on blockwise monotone tuples give
the strict exponent bound at every fundamental coweight. -/
theorem strictFundHypothesis_of_core :
    letI := T.topology
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V), IsSmooth ρ →
    (∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
        IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedJacquet C D ρ).comp
            ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
              ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
        ∀ a : Fin (C.flatten D).length → F.Carrierˣ,
          (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
            T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
          ‖(ψ a : ℂ)‖ ≤ 1 ∧
            ((∃ (j : Fin C.length) (i i' : Fin (D j).length),
                T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier) ≠
                  T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i'⟩) : F.Carrier)) →
              ‖(ψ a : ℂ)‖ < 1)) →
    StrictFundHypothesis T C ρ := by
  let := T.topology
  intro ρ hρ hcore s ψ hgen
  have hopen := isOpen_ker_of_isGeneralizedEigencharacter_refined T C ρ hρ
    (fundRefinement C s) ψ hgen
  have hval : ∀ (j : Fin C.length) (i : Fin (fundRefinement C s j).length),
      flatScalars C (fundRefinement C s) (fundScalars T C s)
          (C.flattenBlockEquiv (fundRefinement C s) ⟨j, i⟩) = fundScalars T C s j i :=
    fun j i => flatScalars_apply C _ _ j i
  have hmono : ∀ j : Fin C.length, Monotone (fun i : Fin (fundRefinement C s j).length =>
      T.normalizedAbs (flatScalars C (fundRefinement C s) (fundScalars T C s)
        (C.flattenBlockEquiv (fundRefinement C s) ⟨j, i⟩) : F.Carrier)) := by
    intro j
    simp only [hval]
    exact monotone_abs_of_isWeaklyContracting T _ _
      (fundScalars_isStrictlyContracting T C s j).weak
  have hlen : (fundRefinement C s s.1).length = 2 := by
    rw [fundRefinement, Function.update_self]
    rfl
  have hne : ∃ (j : Fin C.length) (i i' : Fin (fundRefinement C s j).length),
      T.normalizedAbs (flatScalars C (fundRefinement C s) (fundScalars T C s)
          (C.flattenBlockEquiv (fundRefinement C s) ⟨j, i⟩) : F.Carrier) ≠
        T.normalizedAbs (flatScalars C (fundRefinement C s) (fundScalars T C s)
          (C.flattenBlockEquiv (fundRefinement C s) ⟨j, i'⟩) : F.Carrier) := by
    refine ⟨s.1, ⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    rw [hval, hval]
    have h0 : fundScalars T C s s.1 ⟨0, by omega⟩ =
        LocalFactor.PadicAbelian.uniformizerUnit T := by
      simp [fundScalars, twoScalars]
    have h1 : fundScalars T C s s.1 ⟨1, by omega⟩ = 1 := by
      simp [fundScalars, twoScalars]
    rw [h0, h1, uniformizer_abs, Units.val_one, T.normalizedAbs_one]
    exact (inv_lt_one_of_one_lt₀ (residueCardinality_gt_one_real T)).ne
  exact (hcore (fundRefinement C s) ψ hopen hgen _ hmono).2 hne

/-- An admissible representation satisfying the strict exponent hypothesis has
every absolute matrix coefficient in `L^2` of the central quotient, given the
Cartan coset count. -/
theorem memLp_two_of_strictFundHypothesis
    (hcount : CartanQuotient.CartanCellCountStatement.{uF}) :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (ρ : Representation ℂ (C.Levi F.Carrier) V),
      IsAdmissible ρ → StrictFundHypothesis T C ρ →
      ∀ (c : UnitaryCentralCharacter ρ) (ℓ : SmoothDual ρ) (v : V),
        MeasureTheory.MemLp (c.coefficientNorm (ℓ : Module.Dual ℂ V) v) 2 μ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ ρ hadm hstrict c ℓ v
  classical
  obtain ⟨ε, hε, cb, hcb⟩ := strict_cell_coefficient_bound T C ρ hadm hstrict ℓ v
  obtain ⟨cc, hcc0, hcc⟩ := measure_cellQ_le T C hcount
  set P : ℝ := 2 with hPdef
  have hP : 0 < P := by norm_num
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
    have hκ : ((1 : ℝ) / 2 + ε) * P + -1 = 2 * ε := by
      rw [hPdef]
      ring
    have hxs : x s = w s ^ (((1 : ℝ) / 2 + ε) * P + -1) := by
      simp only [x, y]
      rw [Real.rpow_add (hw0 s) (((1 : ℝ) / 2 + ε) * P) (-1), Real.rpow_mul (hw0 s).le,
        Real.rpow_neg_one]
    rw [hxs, hκ]
    exact Real.rpow_lt_one (hw0 s).le (hw1 s) (by positivity)
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
  have hLp := countableCellLpUpper _ (FundIndex C → ℕ) μ _ (ENNReal.ofReal P) hp0
    ENNReal.ofReal_ne_top hmeas (fun m => cellQ T C (latticeTuple C m)) hcover b hbound hsum
  have hP2 : ENNReal.ofReal P = 2 := by
    rw [hPdef, ENNReal.ofReal_ofNat]
  rwa [hP2] at hLp

/-- The product-Levi square-integrability sufficiency, given the Cartan coset count. -/
theorem squareIntegrable_of_cellCount (hcount : CartanQuotient.CartanCellCountStatement.{uF}) :
    GLProductLeviSquareIntegrableExponentSufficiencyStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ C S ω hirr hadm hω hunit hcore _ _ _ μ _
  let := T.leviTopologicalGroup C
  have : Nontrivial S.V := by
    let := hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (C.Levi F.Carrier)) S.ρ.asModule
  let c := T.unitaryCentralCharacterOfBlockScalar C S.ρ ω hadm.1 hω hunit
  exact ⟨hadm, c, fun ℓ v => memLp_two_of_strictFundHypothesis T C hcount μ S.ρ hadm
    (strictFundHypothesis_of_core T C S.ρ hadm.1 hcore) c ℓ v⟩

end ProductLeviSquareIntegrable

/-- Product-Levi square-integrability modulo the centre from weak and strict
upper generalized Jacquet exponent bounds. -/
theorem glProductLeviSquareIntegrableExponentSufficiency :
    GLProductLeviSquareIntegrableExponentSufficiencyStatement.{uF, uV} :=
  ProductLeviSquareIntegrable.squareIntegrable_of_cellCount
    GeneralLinear.CartanQuotient.cartanCellCount

end Langlands
