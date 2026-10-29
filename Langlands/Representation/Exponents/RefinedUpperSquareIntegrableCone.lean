import Langlands.Representation.Classification.ProductLeviSquareIntegrableExponent

/-!
# Strict blockwise cones for upper exponents of square-integrable product Levis

Let `σ` be a representation of a product Levi `C.Levi F.Carrier` which is square
integrable modulo the full centre for one Borel Haar measure. For every refinement
`D`, a generalized eigencharacter `ψ` of the normalized refined Jacquet module,
pulled back along the flattened scalars, has every real part in the open positive
root cone separately inside each original block.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.Exponents.RefinedUpperSquareIntegrableCone

open GeneralLinear Geometric ProductLeviChamber ProductLeviNecessity MeasureTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On a weakly contracting block-scalar tuple which is central in the original
Levi and has refined modulus one, a generalized eigencharacter of a
square-integrable representation has norm one. -/
theorem norm_eq_one_of_mem_center :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsSquareIntegrableModCenter σ μ →
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
      ‖(ψ (flatScalars C D c) : ℂ)‖ = 1 := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ hsq D ψ hgen c hc hcen hδ
  obtain ⟨hadm, χ, -⟩ := hsq
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
  exact hnorm.symm

/-- The test set of a proper prefix of refined blocks is nonempty. -/
theorem testSet_nonempty (D : BlockRefinement C) (j : Fin C.length) {k : ℕ} (hk : 0 < k)
    (hkD : k < (D j).length) : (testSet C D j k).Nonempty := by
  let l : Fin (D j).length := ⟨0, by omega⟩
  refine ⟨(D j).indexEquiv ⟨l, ⟨0, (D j).positive l⟩⟩, ?_⟩
  simp only [testSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  exact hk

/-- The complement of the test set of a proper prefix of refined blocks is nonempty. -/
theorem testSet_compl_nonempty (D : BlockRefinement C) (j : Fin C.length) {k : ℕ}
    (hkD : k < (D j).length) : (testSet C D j k)ᶜ.Nonempty := by
  let l : Fin (D j).length := ⟨k, hkD⟩
  refine ⟨(D j).indexEquiv ⟨l, ⟨0, (D j).positive l⟩⟩, ?_⟩
  simp only [testSet, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.symm_apply_apply]
  exact lt_irrefl k

/-- The real-part identity at a test tuple. -/
theorem norm_testScalars {D : BlockRefinement C}
    {ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ} {x : Fin (C.flatten D).length → ℝ}
    (hx : T.IsRealPartOf ψ x) (j : Fin C.length) (k : ℕ) (e : ℤ) :
    ‖(ψ (flatScalars C D (testScalars T C D j k e)) : ℂ)‖ =
      (T.residueCardinality : ℝ) ^
        (-(e : ℝ) * partialSum (fun l => x (C.flattenBlockEquiv D ⟨j, l⟩)) k) := by
  rw [(PadicField.TopologicalData.isRealPartOf_iff_pairing T ψ x).mp hx,
    sum_centreHMap_testScalars]

/-- Every proper prefix sum of one original block of a real part is strictly
positive. -/
theorem partialSum_pos :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsSquareIntegrableModCenter σ μ →
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D σ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
      ∀ (j : Fin C.length) (k : ℕ), 0 < k → k < (D j).length →
      0 < partialSum (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩)) k := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ hsq D ψ hgen x hx j k hk hkD
  have hlt := ProductLeviSquareIntegrable.norm_lt_one_of_diagonal T C μ σ hsq D ψ hgen
    (testScalars T C D j k 1) (testScalars_isWeaklyContracting T C D j k) j
    (testSet C D j k) (testSet_nonempty C D j hk hkD) (testSet_compl_nonempty C D j hkD)
    (testScalars_blockScalar_same T C D j k) (testScalars_refinedLeviModulus T C D j k)
  rw [norm_testScalars T C hx j k 1] at hlt
  have hq := T.one_lt_residueCardinality_real
  conv_rhs at hlt => rw [← Real.rpow_zero (T.residueCardinality : ℝ)]
  rw [Real.rpow_lt_rpow_left_iff hq] at hlt
  push_cast at hlt
  linarith

/-- The real-part coordinates of one original block add up to zero. -/
theorem blockSum_eq_zero :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsSquareIntegrableModCenter σ μ →
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D σ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
      ∀ j : Fin C.length, ∑ l : Fin (D j).length, x (C.flattenBlockEquiv D ⟨j, l⟩) = 0 := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ hsq D ψ hgen x hx j
  have h1 := norm_eq_one_of_mem_center T C μ σ hsq D ψ hgen
    (testScalars T C D j (D j).length 1) (testScalars_full_isWeaklyContracting T C D j 1)
    (testScalars_full_mem_center T C D j 1) (testScalars_full_refinedLeviModulus T C D j 1)
  rw [norm_testScalars T C hx j (D j).length 1] at h1
  have hfull : partialSum (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩))
      (D j).length = ∑ l : Fin (D j).length, x (C.flattenBlockEquiv D ⟨j, l⟩) := by
    rw [partialSum]
    congr 1
    exact Finset.filter_true_of_mem fun l _ => l.isLt
  rw [hfull] at h1
  have hq := T.one_lt_residueCardinality_real
  conv_rhs at h1 => rw [← Real.rpow_zero (T.residueCardinality : ℝ)]
  rw [Real.rpow_right_inj (by linarith) hq.ne'] at h1
  push_cast at h1
  linarith

/-- Every real part of a generalized eigencharacter of the normalized refined
Jacquet module lies in the open positive root cone inside each original block. -/
theorem isPositiveRootCone :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ [MeasurableSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      [BorelSpace (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier))]
      (μ : Measure (C.Levi F.Carrier ⧸ Subgroup.center (C.Levi F.Carrier)))
      [μ.IsHaarMeasure] (σ : Representation ℂ (C.Levi F.Carrier) V),
      IsSquareIntegrableModCenter σ μ →
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D σ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
      ∀ j : Fin C.length,
        IsPositiveRootCone (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩)) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ hsq D ψ hgen x hx j
  exact ⟨blockSum_eq_zero T C μ σ hsq D ψ hgen x hx j,
    fun k hk hkD => partialSum_pos T C μ σ hsq D ψ hgen x hx j k hk hkD⟩

end Langlands.Exponents.RefinedUpperSquareIntegrableCone
