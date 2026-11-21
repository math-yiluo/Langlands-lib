import Langlands.BaseChange.WeylIntegrationData
import Langlands.BaseChange.CyclicAlgebraTopology
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic

/-! # Topology of the ordinary Weyl discriminant -/

namespace Langlands.BaseChange

open Filter
open scoped NNReal

private theorem continuous_matrix_charpoly_coeff {R ι : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Continuous (fun M : Matrix ι ι R => M.charpoly.coeff k) := by
  have h : (fun M : Matrix ι ι R => M.charpoly.coeff k) =
      fun M => MvPolynomial.eval (fun ij : ι × ι => M ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom R) ((Matrix.charpoly.univ ℤ ι).coeff k)) := by
    funext M
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom,
      Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)

variable {F : Type*} [Field F] {n : ℕ}

/-- The Weyl discriminant is continuous in the matrix group topology. -/
theorem continuous_weylDiscriminant [TopologicalSpace F] [IsTopologicalRing F] :
    Continuous (weylDiscriminant (F := F) (n := n)) := by
  let b := Matrix.stdBasis F (Fin n) (Fin n)
  have heq : weylDiscriminant = fun γ : GeneralLinear n F =>
        (LinearMap.toMatrix b b (linearAdjoint γ - LinearMap.id)).charpoly.coeff n := by
    funext γ
    rw [LinearMap.charpoly_toMatrix, weylDiscriminant]
  rw [heq]
  apply (continuous_matrix_charpoly_coeff n).comp
  refine continuous_pi fun i => continuous_pi fun j => ?_
  let : IsModuleTopology F (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (IsModuleTopology F (Fin n → Fin n → F))
  have hr : Continuous (fun X : Matrix (Fin n) (Fin n) F => b.repr X i) :=
    IsModuleTopology.continuous_of_linearMap ((Finsupp.lapply i).comp b.repr.toLinearMap)
  have hX : Continuous (fun γ : GeneralLinear n F =>
      γ.val * (b j * (γ⁻¹).val) - b j) :=
    (Units.continuous_val.mul
      (continuous_const.mul (Units.continuous_val.comp continuous_inv))).sub continuous_const
  simp only [LinearMap.toMatrix_apply]
  exact hr.comp hX

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

namespace WeylTorus

/-- The nonnegative absolute Weyl discriminant on the regular point set. -/
noncomputable def discriminantWeight (T : WeylTorus F n) (t : T.regularPoints) : ℝ≥0 :=
  ⟨LocalField.residueNormalizedAbsoluteValue F (weylDiscriminant t.val.val),
    (LocalField.residueNormalizedAbsoluteValue F).nonneg _⟩

/-- A nonzero Weyl discriminant gives a positive weight. -/
theorem discriminantWeight_pos (T : WeylTorus F n) (t : T.regularPoints)
    (hne : weylDiscriminant t.val.val ≠ 0) :
    0 < T.discriminantWeight t :=
  (LocalField.residueNormalizedAbsoluteValue F).pos hne

open scoped WithZeroTopology in
/-- The absolute discriminant is locally constant on the regular torus when
its discriminant is nowhere zero there. -/
theorem isLocallyConstant_discriminantWeight (T : WeylTorus F n)
    (hne : ∀ t : T.regularPoints, weylDiscriminant t.val.val ≠ 0) :
    IsLocallyConstant T.discriminantWeight := by
  let D (t : T.regularPoints) := weylDiscriminant t.val.val
  have hD : Continuous D :=
    continuous_weylDiscriminant.comp (continuous_subtype_val.comp continuous_subtype_val)
  let v := ValuativeRel.valuation F
  have hv : Continuous (fun t : T.regularPoints => v (D t)) :=
    IsValuativeTopology.continuous_valuation.comp hD
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun t => ?_
  have hvne : v (D t) ≠ 0 := v.ne_zero_iff.mpr (hne t)
  filter_upwards [(hv.tendsto t).eventually
    (WithZeroTopology.singleton_mem_nhds_of_ne_zero hvne)] with s hs
  have hval : FML.normalizedMultiplicativeValuation F (D s) =
      FML.normalizedMultiplicativeValuation F (D t) :=
    congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F) hs
  apply Subtype.ext
  change LocalField.residueNormalizedAbsoluteValue F (D s) =
    LocalField.residueNormalizedAbsoluteValue F (D t)
  rw [LocalField.residueNormalizedAbsoluteValue_of_ne_zero F (hne s),
    LocalField.residueNormalizedAbsoluteValue_of_ne_zero F (hne t), hval]

end WeylTorus

end Langlands.BaseChange
