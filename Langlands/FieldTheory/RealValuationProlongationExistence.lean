import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Topology.Algebra.Valued.NormedValued
import Langlands.Analysis.UltrametricCompletion

/-! # Existence of normalized real valuation prolongations -/

noncomputable section

open scoped NNReal

namespace Langlands.FieldTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The real absolute value underlying a real valuation. -/
def realValuationAbsoluteValue (ν : Valuation K ℝ≥0) : AbsoluteValue K ℝ where
  toFun x := ν x
  map_mul' x y := by simp only [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by simp only [NNReal.coe_eq_zero, Valuation.zero_iff]
  add_le' x y := (NNReal.coe_le_coe.mpr (ν.map_add x y)).trans
    (by
      rw [NNReal.coe_max]
      exact max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

/-- Any real valuation prolongs, with its normalization unchanged, to an
algebraic field extension. Henselianity is not needed for existence. -/
theorem exists_realValuation_prolongation [Algebra.IsAlgebraic K Ω]
    (ν : Valuation K ℝ≥0) :
    ∃ w : Valuation Ω ℝ≥0, w.comap (algebraMap K Ω) = ν := by
  classical
  by_cases hn : ν.IsNontrivial
  · let : NormedField K := (realValuationAbsoluteValue ν).toNormedField
    let : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne (by
      obtain ⟨x, hx0, hx1⟩ := hn.exists_val_nontrivial
      refine ⟨x, ν.ne_zero_iff.mp hx0, ?_⟩
      change (ν x : ℝ) ≠ 1
      exact_mod_cast hx1)
    let : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (fun x y => NNReal.coe_le_coe.mpr (ν.map_add x y))
    let C := UniformSpace.Completion K
    let : NontriviallyNormedField C :=
      { (inferInstance : NormedField C) with
        non_trivial := by
          obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
          refine ⟨(x : C), ?_⟩
          change 1 < ‖(x : UniformSpace.Completion K)‖
          rw [UniformSpace.Completion.norm_coe]
          exact hx }
    let A := AlgebraicClosure C
    let : Algebra K A := ((algebraMap C A).comp (algebraMap K C)).toAlgebra
    let : NontriviallyNormedField A := spectralNorm.nontriviallyNormedField C A
    let : IsUltrametricDist A := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (fun x y => isNonarchimedean_spectralNorm (K := C) (L := A) x y)
    let f : Ω →ₐ[K] A := IsAlgClosed.lift
    refine ⟨(NormedField.valuation (K := A)).comap f.toRingHom, ?_⟩
    apply Valuation.ext
    intro x
    change ‖f (algebraMap K Ω x)‖₊ = ν x
    rw [f.commutes]
    apply NNReal.coe_injective
    change spectralNorm C A (algebraMap C A (algebraMap K C x)) = (ν x : ℝ)
    rw [spectralNorm_extends]
    exact UniformSpace.Completion.norm_coe x
  · refine ⟨1, ?_⟩
    apply Valuation.ext
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [Valuation.comap_apply, Valuation.one_apply_of_ne_zero
        ((map_ne_zero_iff _ (algebraMap K Ω).injective).mpr hx)]
      by_contra h
      exact hn ⟨x, ν.ne_zero_iff.mpr hx, fun hx1 => h hx1.symm⟩

/-- A chosen normalized real prolongation to an algebraic extension. -/
def realValuationProlongation [Algebra.IsAlgebraic K Ω]
    (ν : Valuation K ℝ≥0) : Valuation Ω ℝ≥0 :=
  (exists_realValuation_prolongation (Ω := Ω) ν).choose

@[simp] theorem realValuationProlongation_comap [Algebra.IsAlgebraic K Ω]
    (ν : Valuation K ℝ≥0) :
    (realValuationProlongation (Ω := Ω) ν).comap (algebraMap K Ω) = ν :=
  (exists_realValuation_prolongation (Ω := Ω) ν).choose_spec

end Langlands.FieldTheory
