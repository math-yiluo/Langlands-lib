import Langlands.HarmonicAnalysis.PadicLatticeHaarStatement
import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.LocalField.Uniformizer

/-! Haar masses of the actual valuation lattices, and conductor normalization. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Langlands.HarmonicAnalysis

universe u

private theorem latticeHaarMass {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (μ : AdditiveHaarMeasure F.Carrier) (m : ℤ),
      μ.measure (T.additiveLattice m : Set F.Carrier) < ∞ ∧
      0 < (μ.measure (T.additiveLattice m : Set F.Carrier)).toReal ∧
      (μ.measure (T.additiveLattice m : Set F.Carrier)).toReal =
        (T.residueCardinality : ℝ) ^ m *
          (μ.measure (T.additiveLattice 0 : Set F.Carrier)).toReal := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro μ m
  have hfin := (T.isCompact_additiveLattice m).measure_lt_top (μ := μ.measure)
  have hpos := (T.isOpen_additiveLattice m).measure_pos μ.measure
    ⟨0, (T.additiveLattice m).zero_mem⟩
  refine ⟨hfin, ENNReal.toReal_pos hpos.ne' hfin.ne, ?_⟩
  let a : F.Carrierˣ := LocalFactor.PadicAbelian.uniformizerUnit T ^ m
  have hpre : (fun x : F.Carrier => (a : F.Carrier) * x) ⁻¹'
      (T.Integers : Set F.Carrier) = (T.additiveLattice m : Set F.Carrier) := by
    ext x
    rw [SetLike.mem_coe, T.mem_additiveLattice_iff_div_mem_integers]
    simp only [Set.mem_preimage, a, Units.val_zpow_eq_zpow_val,
      LocalFactor.PadicAbelian.uniformizerUnit_coe, zpow_neg, div_inv_eq_mul, mul_comm]
    rfl
  have hscale := congrArg
    (fun ν : Measure F.Carrier => (ν (T.Integers : Set F.Carrier)).toReal)
    (padicScalarHaarScaling F T μ.measure a)
  rw [Measure.map_apply (f := fun x : F.Carrier => (a : F.Carrier) * x)
    (continuous_const.mul continuous_id).measurable
    T.isOpen_integers.measurableSet, hpre, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_inv,
    T.normalizedAbsUnits_coe,
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T m, zpow_neg, inv_inv] at hscale
  have hzero : (T.additiveLattice 0 : Set F.Carrier) =
      (T.Integers : Set F.Carrier) := Set.ext (T.mem_additiveLattice_zero)
  simpa only [hzero] using hscale

/-- Valuation-lattice Haar masses and a conductor-normalized regular additive
Haar measure for every supplied p-adic topology. -/
theorem padicLatticeHaar {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    PadicLatticeHaarStatement F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  refine ⟨latticeHaarMass F T, ?_⟩
  intro ψ
  let := T.fieldT2
  let K : TopologicalSpace.PositiveCompacts F.Carrier :=
    ⟨⟨(T.Integers : Set F.Carrier), T.isCompact_integers⟩, by
      rw [T.isOpen_integers.interior_eq]
      exact ⟨0, T.Integers.zero_mem⟩⟩
  let μ := normalizedAdditiveHaar F.Carrier K
  have hμO : μ.measure (T.Integers : Set F.Carrier) = 1 :=
    Measure.addHaarMeasure_self
  have hzero : (T.additiveLattice 0 : Set F.Carrier) =
      (T.Integers : Set F.Carrier) := Set.ext (T.mem_additiveLattice_zero)
  have hμ0 : (μ.measure (T.additiveLattice 0 : Set F.Carrier)).toReal = 1 := by
    rw [hzero, hμO, ENNReal.toReal_one]
  have hq : 0 < (T.residueCardinality : ℝ) := by
    exact_mod_cast lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  have hqn : 0 < (T.residueCardinality : ℝ) ^ T.additiveConductor ψ :=
    zpow_pos hq _
  have hs : 0 < Real.sqrt ((T.residueCardinality : ℝ) ^ T.additiveConductor ψ) :=
    Real.sqrt_pos.2 hqn
  let c : ℝ≥0 := ⟨(Real.sqrt
    ((T.residueCardinality : ℝ) ^ T.additiveConductor ψ))⁻¹, (inv_pos.mpr hs).le⟩
  have hc : c ≠ 0 := by
    intro hc
    exact (inv_pos.mpr hs).ne' (congrArg (fun r : ℝ≥0 => (r : ℝ)) hc)
  let ν : AdditiveHaarMeasure F.Carrier :=
    ⟨c • μ.measure, Measure.IsAddHaarMeasure.nnreal_smul _ hc, inferInstance⟩
  have hmass (m : ℤ) :
      (ν.measure (T.additiveLattice m : Set F.Carrier)).toReal =
        (T.residueCardinality : ℝ) ^ m /
          Real.sqrt ((T.residueCardinality : ℝ) ^ T.additiveConductor ψ) := by
    change ((c • μ.measure) (T.additiveLattice m : Set F.Carrier)).toReal = _
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.coe_toReal, (latticeHaarMass F T μ m).2.2, hμ0, mul_one]
    exact mul_comm _ _
  refine ⟨ν, fun m => ⟨hmass m, ?_⟩⟩
  rw [hmass m, hmass (T.additiveConductor ψ - m), div_mul_div_comm,
    ← zpow_add₀ hq.ne', add_sub_cancel,
    ← pow_two, Real.sq_sqrt hqn.le, div_self hqn.ne']

end Langlands.HarmonicAnalysis
