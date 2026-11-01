import Langlands.Representation.Exponents.RefinedUpperTemperedConeStatement
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof
import Langlands.Representation.Exponents.RefinedUpperSquareIntegrableCone
import Langlands.Representation.Exponents.WeightedBlockCone

/-! Closed upper cones for actual generalized tempered exponents. -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.Exponents.RefinedUpperTemperedCone

open GeneralLinear Geometric ProductLeviChamber ProductLeviNecessity MeasureTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem partialSum_nonneg :
    letI := T.topology
    letI := T.leviTopologicalGroup C
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
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
      ∀ (j : Fin C.length) (k : ℕ),
      0 ≤ partialSum (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩)) k := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ htemp D ψ hgen x hx j k
  have hle := norm_le_one_of_diagonal T C μ σ htemp D ψ hgen
    (testScalars T C D j k 1) (testScalars_isWeaklyContracting T C D j k) j
    (testSet C D j k) (testScalars_blockScalar_same T C D j k)
    (testScalars_refinedLeviModulus T C D j k)
  rw [RefinedUpperSquareIntegrableCone.norm_testScalars T C hx j k 1] at hle
  conv_rhs at hle => rw [← Real.rpow_zero (T.residueCardinality : ℝ)]
  rw [Real.rpow_le_rpow_left_iff T.one_lt_residueCardinality_real] at hle
  push_cast at hle
  linarith

theorem blockSum_eq_zero :
    letI := T.topology
    letI := T.leviTopologicalGroup C
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
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
      ∀ j : Fin C.length, ∑ l : Fin (D j).length, x (C.flattenBlockEquiv D ⟨j, l⟩) = 0 := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ htemp D ψ hgen x hx j
  have hlo := partialSum_nonneg T C μ σ htemp D ψ hgen x hx j (D j).length
  have hhi := norm_le_one_of_mem_center T C μ σ htemp D ψ hgen
    (testScalars T C D j (D j).length (-1))
    (testScalars_full_isWeaklyContracting T C D j (-1))
    (testScalars_full_mem_center T C D j (-1))
    (testScalars_full_refinedLeviModulus T C D j (-1))
  rw [RefinedUpperSquareIntegrableCone.norm_testScalars T C hx j (D j).length (-1)] at hhi
  conv_rhs at hhi => rw [← Real.rpow_zero (T.residueCardinality : ℝ)]
  rw [Real.rpow_le_rpow_left_iff T.one_lt_residueCardinality_real] at hhi
  have hfull : partialSum (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩))
      (D j).length = ∑ l : Fin (D j).length, x (C.flattenBlockEquiv D ⟨j, l⟩) := by
    rw [partialSum]
    congr 1
    exact Finset.filter_true_of_mem fun l _ => l.isLt
  rw [hfull] at hlo hhi
  push_cast at hhi
  linarith

theorem isClosedPositiveRootCone :
    letI := T.topology
    letI := T.leviTopologicalGroup C
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
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
      ∀ j : Fin C.length,
        IsClosedPositiveRootCone
          (fun l : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, l⟩)) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ htemp D ψ hgen x hx j
  exact ⟨blockSum_eq_zero T C μ σ htemp D ψ hgen x hx j,
    fun k _ _ => partialSum_nonneg T C μ σ htemp D ψ hgen x hx j k⟩

/-- Divide a fine scalar exponent by its fine size before repeating it on the
diagonal. This preserves each source block's closed positive cone. -/
theorem diagonalized_isClosedPositiveRootCone :
    letI := T.topology
    letI := T.leviTopologicalGroup C
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
      ∀ x : Fin (C.flatten D).length → ℝ, T.IsRealPartOf ψ x →
      ∀ j : Fin C.length,
        IsClosedPositiveRootCone (fun a : Fin (C.size j) =>
          x (C.flattenBlockEquiv D ⟨j, blockIndex (D j) a⟩) /
            ((D j).size (blockIndex (D j) a) : ℝ)) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro _ _ μ _ σ htemp D ψ hgen x hx j
  apply diagonal_cone_of_weighted_block_cone (D j)
    (fun l => x (C.flattenBlockEquiv D ⟨j, l⟩) / ((D j).size l : ℝ))
  have hsize (l : Fin (D j).length) : ((D j).size l : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr ((D j).positive l)).ne'
  simpa only [mul_div_cancel₀ _ (hsize _)] using
    isClosedPositiveRootCone T C μ σ htemp D ψ hgen x hx j

end Langlands.Exponents.RefinedUpperTemperedCone

namespace Langlands.Exponents

universe uF uV

open GeneralLinear Geometric MeasureTheory

/-- Actual generalized upper refined exponents of a tempered product Levi satisfy
both the fine scalar and the divided diagonal closed-cone inequalities. -/
theorem refinedUpperTemperedCone : RefinedUpperTemperedConeStatement.{uF,uV} := by
  intro p _ F T
  let := T.topology
  intro n C
  let := T.leviTopologicalGroup C
  intro _ _ μ _ V _ _ σ htemp D ψ hgen x hx
  exact ⟨RefinedUpperTemperedCone.isClosedPositiveRootCone T C μ σ htemp D ψ hgen x hx,
    RefinedUpperTemperedCone.diagonalized_isClosedPositiveRootCone
      T C μ σ htemp D ψ hgen x hx⟩

end Langlands.Exponents
