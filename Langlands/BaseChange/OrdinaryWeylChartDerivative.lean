import Langlands.BaseChange.OrbitChartDerivative
import Langlands.BaseChange.OrdinaryWeylDifferential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # The strict derivative in ordinary Weyl coordinates -/

noncomputable section

open scoped Matrix.Norms.Operator

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u

private abbrev Mat (F : Type u) (n : ℕ) := Matrix (Fin n) (Fin n) F

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] {n : ℕ}

/-- Projection from the matrix Lie algebra onto the ordinary centralizer Lie
algebra along the adjoint defect image. -/
def ordinaryWeylTorusProjection (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ) :
    Mat F n →L[F] Mat F n :=
  let d := adjointDefect γ
  LinearMap.toContinuousLinearMap
    (d.ker.projection d.range (isCompl_ker_range_adjointDefect γ hγ))

/-- The right-normalized ordinary Weyl chart based at `γ`. -/
def ordinaryWeylChart (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ) :
    Mat F n → Mat F n :=
  let I := ContinuousLinearMap.id F (Mat F n)
  let P := ordinaryWeylTorusProjection γ hγ
  normalizedOrbitChart γ I P (I - P)

@[simp]
theorem ordinaryWeylChart_zero (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ) :
    ordinaryWeylChart γ hγ 0 = 1 :=
  normalizedOrbitChart_zero γ _ rfl _ _

/-- The ordinary chart has an invertible strict derivative with determinant
the Library Weyl discriminant. -/
abbrev OrdinaryWeylChartDerivativeStatement : Prop :=
  ∀ {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] {n : ℕ}
    (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ),
    let D := ordinaryWeylTorusProjection γ hγ -
      LinearMap.toContinuousLinearMap (adjointDefect γ)
    HasStrictFDerivAt (ordinaryWeylChart γ hγ) D 0 ∧
      IsUnit D.det ∧ D.det = weylDiscriminant γ

theorem ordinaryWeylChartDerivative : OrdinaryWeylChartDerivativeStatement.{u} := by
  intro F _ _ n γ hγ
  have hseries : HasSummableGeomSeries (Mat F n) := by
    refine @instHasSummableGeomSeriesOfCompleteSpace _ _ ?_
    change CompleteSpace (Fin n → Fin n → F)
    infer_instance
  let I := ContinuousLinearMap.id F (Mat F n)
  let d := adjointDefect γ
  let P := ordinaryWeylTorusProjection γ hγ
  let Q := I - P
  let A : Mat F n →L[F] Mat F n :=
    ContinuousLinearMap.mulLeftRight F (Mat F n) γ.val (γ⁻¹ : GeneralLinear n F).val
  let D := P - LinearMap.toContinuousLinearMap d
  change HasStrictFDerivAt (ordinaryWeylChart γ hγ) D 0 ∧
    IsUnit D.det ∧ D.det = weylDiscriminant γ
  refine ⟨?_, det_ordinaryWeylDifferential γ hγ⟩
  have h := @orbitChartDerivative F (Mat F n) (Mat F n) _ _ _ _ _ hseries γ I rfl P Q
  change HasStrictFDerivAt (ordinaryWeylChart γ hγ) (Q + P - A.comp (I.comp Q)) 0 at h
  have hderiv : Q + P - A.comp (I.comp Q) = D := by
    apply ContinuousLinearMap.ext
    intro x
    have hdP : d (P x) = 0 :=
      LinearMap.mem_ker.mp (Submodule.projection_apply_mem
        (isCompl_ker_range_adjointDefect γ hγ) x)
    have hA : A (Q x) = d (Q x) + Q x := by
      change γ.val * Q x * (γ⁻¹ : GeneralLinear n F).val = adjointDefect γ (Q x) + Q x
      rw [adjointDefect_apply, sub_add_cancel]
    change Q x + P x - A (Q x) = P x - d x
    have hdQ : d (Q x) = d x := by
      change d (x - P x) = d x
      rw [map_sub, hdP, sub_zero]
    rw [hA, hdQ]
    abel
  exact hderiv ▸ h

end Langlands.BaseChange
