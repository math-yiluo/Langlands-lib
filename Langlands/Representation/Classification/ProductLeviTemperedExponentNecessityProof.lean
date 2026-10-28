import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityStatement
import Langlands.Representation.Classification.ProductLeviNecessityCells
import Langlands.Representation.Classification.ProductLeviNecessityEigen
import Langlands.Representation.Classification.ProductLeviNecessityTest

/-!
# Necessary upper Jacquet bounds for an analytically tempered product Levi

A generalized eigencharacter `ψ` of the normalized refined Jacquet module of an
analytically tempered representation has `|ψ(c)| ≤ 1` on the test elements of
`ProductLeviNecessityCombinatorics`; that reduction then gives the bound on the
whole chamber.

For a test element whose block scalars form the diagonal matrix with the
uniformizer on a set `S` of coordinates of one block, the matrix coefficient of a
compression eigenvector is `λ ^ M ℓ(x)` on the cells `K g ^ M K`, where
`λ = √δ(g) ψ(g)` and `δ(g) = q ^ (-|S| |Sᶜ|)`. Counting `q ^ (m |S| |Sᶜ|)`
disjoint cells modulo the centre and comparing with the finite
`L ^ (2 + ε)`-integral gives `q ^ (|S| |Sᶜ|) |λ| ^ (2 + ε) ≤ 1` for every
`ε > 0`, hence `|ψ(g)| ≤ 1`. For a central test element the unitary central
character gives `|λ| = 1` directly.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal Topology

namespace Langlands.ProductLeviNecessity

open GeneralLinear Geometric ProductLeviChamber MeasureTheory

universe uF uV

/-- A real number `y` with `(2 + ε) y ≤ ε B` for every `ε > 0` is nonpositive. -/
theorem nonpos_of_forall_mul_le {y B : ℝ} (hB : 0 ≤ B)
    (h : ∀ ε : ℝ, 0 < ε → (2 + ε) * y ≤ ε * B) : y ≤ 0 := by
  by_contra hy
  have hy' : 0 < y := lt_of_not_ge hy
  have hB1 : 0 < B + 1 := by linarith
  have hε : 0 < y / (B + 1) := div_pos hy' hB1
  have h1 := h _ hε
  have h2 : y / (B + 1) * (B + 1) = y := div_mul_cancel₀ y hB1.ne'
  nlinarith [mul_pos hε hy']

/-- A real number whose powers stay bounded after multiplication by a positive
constant is at most one. -/
theorem le_one_of_forall_pow_mul_le {R C0 I : ℝ} (hC0 : 0 < C0)
    (h : ∀ m : ℕ, R ^ m * C0 ≤ I) : R ≤ 1 := by
  by_contra hR
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (I / C0) (lt_of_not_ge hR)
  have h1 := h m
  rw [div_lt_iff₀ hC0] at hm
  linarith

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The bound for a weakly contracting block-scalar tuple whose `j`-th block is
the diagonal matrix with the uniformizer on `S` and `1` elsewhere, and whose
refined modulus is `q ^ (-|S| |Sᶜ|)`. -/
theorem norm_le_one_of_diagonal :
    letI := T.topology
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsTemperedModCenter σ μ →
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D σ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ (c : ∀ i, Fin (D i).length → F.Carrierˣ), (∀ i, (D i).IsWeaklyContracting T (c i)) →
      ∀ (j : Fin C.length) (S : Finset (Fin (C.size j))),
      ((D j).blockScalar F.Carrier (c j) : Matrix (Fin (C.size j)) (Fin (C.size j)) F.Carrier) =
        Matrix.diagonal (fun a => if a ∈ S then T.uniformizer else 1) →
      ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) =
        (T.residueCardinality : ℝ) ^ (-((S.card * Sᶜ.card : ℕ) : ℤ)) →
      ‖(ψ (flatScalars C D c) : ℂ)‖ ≤ 1 := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ htemp D ψ hgen c hc j S hg hδ
  obtain ⟨hadm, χ, hLp⟩ := htemp
  obtain ⟨K, -, hKU, ℓ, x, hℓx, hxK, hℓK, hcoef⟩ :=
    exists_eigen_coefficient T C σ hadm D ψ hgen
      (ProductLeviTempered.integralLevi T C).mem_nhds_one c hc
  set g : C.Levi F.Carrier := fun i => (D i).blockScalar F.Carrier (c i) with hg_def
  set lam := compressionEigenvalue T C D ψ c with hlam
  set P : ℕ := S.card * Sᶜ.card with hP
  set q : ℝ := (T.residueCardinality : ℝ) with hq
  have hq1 : 1 < q := T.one_lt_residueCardinality_real
  have hq0 : 0 < q := by linarith
  have hcell : ∀ M : ℕ, ∀ u ∈ K, ∀ k ∈ K,
      matrixCoefficient σ (ℓ : Module.Dual ℂ V) x (u * g ^ M * k) =
        lam ^ M * (ℓ : Module.Dual ℂ V) x := by
    intro M u hu k hk
    change (ℓ : Module.Dual ℂ V) (σ (u * g ^ M * k) x) = _
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hxK k hk, hℓK u hu]
    exact hcoef M
  set δ : ℝ := ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
    ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) with hδdef
  have hδpos : 0 < δ := by
    rw [hδ]
    exact zpow_pos hq0 _
  have hψpos : 0 < ‖(ψ (flatScalars C D c) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hlamnorm : ‖lam‖ = Real.sqrt δ * ‖(ψ (flatScalars C D c) : ℂ)‖ := by
    rw [hlam, compressionEigenvalue, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hlampos : 0 < ‖lam‖ := by
    rw [hlamnorm]
    exact mul_pos (Real.sqrt_pos.mpr hδpos) hψpos
  have hℓpos : 0 < ‖(ℓ : Module.Dual ℂ V) x‖ := norm_pos_iff.mpr hℓx
  set s := μ (QuotientGroup.mk '' (K : Set (C.Levi F.Carrier))) with hs
  have hs0 : 0 < s :=
    (QuotientGroup.isOpenMap_coe _ K.isOpen).measure_pos μ
      ⟨_, Set.mem_image_of_mem _ K.one_mem⟩
  have hstop : s < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono hKU))
      (ProductLeviTempered.measure_image_integralLevi_lt_top T C μ)
  have hspos : 0 < s.toReal := ENNReal.toReal_pos hs0.ne' hstop.ne
  have key : ∀ ε : ℝ, 0 < ε → q ^ P * ‖lam‖ ^ (2 + ε) ≤ 1 := by
    intro ε hε
    have hr : 0 < 2 + ε := by linarith
    let f : C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier) → ℝ≥0∞ :=
      fun z => ‖χ.coefficientNorm (ℓ : Module.Dual ℂ V) x z‖ₑ ^ (2 + ε)
    have hI : ∫⁻ z, f z ∂μ < ⊤ := by
      have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by simpa using hr) ENNReal.ofReal_ne_top (hLp ℓ x ε hε).eLpNorm_lt_top
      rwa [ENNReal.toReal_ofReal hr.le] at h
    obtain ⟨t, ht⟩ := cells_lower_bound T C j S hg K hKU μ f
      (fun M => ‖lam ^ M * (ℓ : Module.Dual ℂ V) x‖ₑ ^ (2 + ε)) (by
        intro M u hu k hk
        refine le_of_eq ?_
        show _ = ‖χ.coefficientNorm (ℓ : Module.Dual ℂ V) x
          (QuotientGroup.mk (u * g ^ M * k))‖ₑ ^ (2 + ε)
        rw [UnitaryCentralCharacter.coefficientNorm_mk, hcell M u hu k hk, enorm_norm])
    refine le_one_of_forall_pow_mul_le
      (C0 := (‖lam‖ ^ (2 + ε)) ^ t * ‖(ℓ : Module.Dual ℂ V) x‖ ^ (2 + ε) * s.toReal)
      (I := (∫⁻ z, f z ∂μ).toReal)
      (mul_pos (mul_pos (pow_pos (Real.rpow_pos_of_pos hlampos _) _)
        (Real.rpow_pos_of_pos hℓpos _)) hspos) fun m => ?_
    have h := ENNReal.toReal_mono hI.ne (ht m)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm,
      ENNReal.toReal_pow, ENNReal.toReal_natCast] at h
    have e1 : ‖lam ^ (m + t) * (ℓ : Module.Dual ℂ V) x‖ ^ (2 + ε) =
        (‖lam‖ ^ (2 + ε)) ^ m * (‖lam‖ ^ (2 + ε)) ^ t *
          ‖(ℓ : Module.Dual ℂ V) x‖ ^ (2 + ε) := by
      rw [norm_mul, norm_pow, Real.mul_rpow (by positivity) (norm_nonneg _),
        ← Real.rpow_pow_comm (norm_nonneg _), pow_add]
    rw [e1] at h
    calc (q ^ P * ‖lam‖ ^ (2 + ε)) ^ m *
          ((‖lam‖ ^ (2 + ε)) ^ t * ‖(ℓ : Module.Dual ℂ V) x‖ ^ (2 + ε) * s.toReal) =
        q ^ (m * P) * ((‖lam‖ ^ (2 + ε)) ^ m * (‖lam‖ ^ (2 + ε)) ^ t *
          ‖(ℓ : Module.Dual ℂ V) x‖ ^ (2 + ε) * s.toReal) := by
          rw [mul_pow, ← pow_mul, mul_comm P m]
          ring
      _ ≤ _ := h
  have hlog : ∀ ε : ℝ, 0 < ε →
      (2 + ε) * Real.log ‖(ψ (flatScalars C D c) : ℂ)‖ ≤ ε * (P * Real.log q / 2) := by
    intro ε hε
    have h := Real.log_nonpos (by positivity) (key ε hε)
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hlampos _).ne', Real.log_pow,
      Real.log_rpow hlampos, hlamnorm, Real.log_mul (Real.sqrt_pos.mpr hδpos).ne' hψpos.ne',
      Real.log_sqrt hδpos.le, hδ, Real.log_zpow] at h
    push_cast at h
    linarith
  have hy := nonpos_of_forall_mul_le
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hq1.le)) zero_le_two) hlog
  exact (Real.log_nonpos_iff hψpos.le).mp hy

/-- The bound for a weakly contracting block-scalar tuple whose block scalars are
central and whose refined modulus is one. -/
theorem norm_le_one_of_mem_center :
    letI := T.topology
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsTemperedModCenter σ μ →
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D σ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ (c : ∀ i, Fin (D i).length → F.Carrierˣ), (∀ i, (D i).IsWeaklyContracting T (c i)) →
      (fun i => (D i).blockScalar F.Carrier (c i) : C.Levi F.Carrier) ∈
        Subgroup.center (C.Levi F.Carrier) →
      ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) = 1 →
      ‖(ψ (flatScalars C D c) : ℂ)‖ ≤ 1 := by
  let := T.topology
  intro _ _ μ _ σ htemp D ψ hgen c hc hcen hδ
  obtain ⟨hadm, χ, -⟩ := htemp
  obtain ⟨K, -, -, ℓ, x, hℓx, -, -, hcoef⟩ :=
    exists_eigen_coefficient T C σ hadm D ψ hgen Filter.univ_mem c hc
  have h1 := hcoef 1
  rw [pow_one, pow_one] at h1
  have hact := χ.acts ⟨_, hcen⟩ x
  change σ (fun i => (D i).blockScalar F.Carrier (c i)) x = _ at hact
  rw [hact, map_smul, smul_eq_mul] at h1
  have heq := mul_right_cancel₀ hℓx h1
  have hnorm := congrArg norm heq
  rw [χ.norm_eq_one, compressionEigenvalue, hδ, Real.sqrt_one, Complex.ofReal_one, one_mul]
    at hnorm
  exact hnorm.symm.le

end Langlands.ProductLeviNecessity

namespace Langlands

open GeneralLinear Geometric ProductLeviNecessity

universe uF uV

/-- Analytic temperedness for one Borel Haar measure on the product-Levi central
quotient forces every upper refined generalized exponent to have norm at most one
on the chamber increasing separately inside each outer block. -/
theorem glProductLeviTemperedExponentNecessity :
    GLProductLeviTemperedExponentNecessityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ B M Q _ _ μ _ V _ _ σ _ htemp D ψ hψ hgen a ha
  exact norm_le_one_of_test T B D ψ hψ
    (fun j k _ _ => norm_le_one_of_diagonal T B μ σ htemp D ψ hgen _
      (testScalars_isWeaklyContracting T B D j k) j _
      (testScalars_blockScalar_same T B D j k) (testScalars_refinedLeviModulus T B D j k))
    (fun j => norm_le_one_of_mem_center T B μ σ htemp D ψ hgen _
      (testScalars_full_isWeaklyContracting T B D j (-1))
      (testScalars_full_mem_center T B D j (-1)) (testScalars_full_refinedLeviModulus T B D j (-1)))
    a ha

end Langlands
