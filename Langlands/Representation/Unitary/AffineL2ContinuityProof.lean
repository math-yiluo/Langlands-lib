import Langlands.Representation.Unitary.AffineL2ContinuityStatement
import Langlands.Analysis.NormalizedL2PullbackContinuityProof

/-! # Continuity of the actual normalized affine L² action: proof -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AffineL2

universe u

private theorem isLocallyConstant_of_isOpen_ker
    {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : G →* H) (ho : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant χ := by
  apply (IsLocallyConstant.iff_exists_open χ).mpr
  intro x
  refine ⟨(fun y : G => y * x⁻¹) ⁻¹' (χ.ker : Set G),
    ho.preimage (continuous_id.mul continuous_const), ?_, ?_⟩
  · simp
  · intro y hy
    change χ (y * x⁻¹) = 1 at hy
    have hy' : χ y * (χ x)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using hy
    exact mul_inv_eq_one.mp hy'

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

private theorem isLocallyConstant_determinantNorm (n : ℕ) :
    letI := T.topology
    IsLocallyConstant (fun A : GeneralLinear n F.Carrier =>
      (T.determinantNorm n A : ℝ≥0)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (isLocallyConstant_of_isOpen_ker (T.determinantNorm n)
    (T.isOpen_ker_determinantNorm n)).comp (fun a : ℝ≥0ˣ => (a : ℝ≥0))

/-- Joint continuity of the actual normalized inverse-affine action. -/
theorem continuous_operator {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      Continuous (fun zf :
          (GeneralLinear n F.Carrier × (Fin n → F.Carrier)) × Lp ℂ 2 μ =>
        operator F T μ zf.1.1 zf.1.2 zf.2) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  intro _ _ μ _
  have he : Continuous (fun qx :
      (GeneralLinear n F.Carrier × (Fin n → F.Carrier)) × (Fin n → F.Carrier) =>
      (AffineChangeOfVariables.measurableEquiv qx.1.1 qx.1.2).symm qx.2) := by
    change Continuous (fun qx :
      (GeneralLinear n F.Carrier × (Fin n → F.Carrier)) × (Fin n → F.Carrier) =>
      (qx.1.1⁻¹).val.mulVec (qx.2 - qx.1.2))
    exact (Units.continuous_coe_inv.comp
      (continuous_fst.comp continuous_fst)).matrix_mulVec
        (continuous_snd.sub (continuous_snd.comp continuous_fst))
  exact NormalizedL2Pullback.locallyConstantScalingContinuity
    (X := Fin n → F.Carrier) (Y := Fin n → F.Carrier)
    (Z := GeneralLinear n F.Carrier × (Fin n → F.Carrier)) μ μ
    (fun q => (AffineChangeOfVariables.measurableEquiv q.1 q.2).symm)
    (fun q => (T.determinantNorm n q.1 : ℝ≥0))
    (fun q => (T.determinantNorm n q.1).ne_zero)
    (fun q => AffineChangeOfVariables.padic_map_haar_symm F T n μ q.1 q.2)
    he ((isLocallyConstant_determinantNorm F T n).comp_continuous continuous_fst)

/-- Joint continuity of the actual mirabolic representation on its L² carrier. -/
theorem continuous_mirabolicRepresentation {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      Continuous (fun gf : GeneralLinear.mirabolic n F.Carrier × Lp ℂ 2 μ =>
        mirabolicRepresentation F T μ gf.1 gf.2) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _
  change Continuous (fun gf : GeneralLinear.mirabolic n F.Carrier × Lp ℂ 2 μ =>
    operator F T μ (GeneralLinear.Mirabolic.linearPart gf.1)
      (GeneralLinear.Mirabolic.columnPart gf.1) gf.2)
  have hcoord : Continuous
      (fun gf : GeneralLinear.mirabolic n F.Carrier × Lp ℂ 2 μ =>
        ((GeneralLinear.Mirabolic.linearPart gf.1,
          GeneralLinear.Mirabolic.columnPart gf.1), gf.2)) :=
    (((GeneralLinear.Mirabolic.continuous_linearPart.prodMk
      GeneralLinear.Mirabolic.continuous_columnPart).comp continuous_fst).prodMk
        continuous_snd)
  have hcont := (continuous_operator (n := n) F T μ).comp hcoord
  exact hcont

/-- The actual normalized affine and mirabolic L² actions are jointly continuous. -/
theorem jointContinuity : JointContinuity F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n _ _ μ _
  exact ⟨continuous_operator F T μ, continuous_mirabolicRepresentation F T μ⟩

end Langlands.AffineL2
