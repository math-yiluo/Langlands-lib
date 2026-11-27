import Langlands.BaseChange.TwistedLocalDescent.MatrixNorm
import Langlands.Analysis.Local.UnitsCoordinateBall

/-! # The sup-norm matrix ring and its congruence balls

Over an ultrametric nontrivially normed field the entrywise sup norm makes square matrices a
normed algebra. Over a complete, proper such field, for small positive radii `r` the elements `g`
of `GL_n` with `‖g − 1‖ ≤ r` form a compact open subgroup, and the coordinate map `g ↦ g − 1` has
image the closed matrix ball of radius `r`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Metric Set Langlands

universe v

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] {n : ℕ}

/-- The entrywise sup norm as a normed ring structure. -/
@[reducible]
def matrixSupNormedRing : NormedRing (Matrix (Fin n) (Fin n) 𝕂) :=
  { (Matrix.normedAddCommGroup : NormedAddCommGroup (Matrix (Fin n) (Fin n) 𝕂)),
    (inferInstance : Ring (Matrix (Fin n) (Fin n) 𝕂)) with
    norm_mul_le := matrix_norm_mul_le }

attribute [local instance] matrixSupNormedRing

/-- The entrywise sup norm as a normed algebra structure. -/
@[reducible]
def matrixSupNormedAlgebra : NormedAlgebra 𝕂 (Matrix (Fin n) (Fin n) 𝕂) :=
  { (inferInstance : Algebra 𝕂 (Matrix (Fin n) (Fin n) 𝕂)) with
    norm_smul_le := fun c X => (norm_smul c X).le }

attribute [local instance] matrixSupNormedAlgebra

variable [CompleteSpace 𝕂] [ProperSpace 𝕂]

omit [CompleteSpace 𝕂] in
theorem matrix_properSpace : ProperSpace (Matrix (Fin n) (Fin n) 𝕂) :=
  (inferInstance : ProperSpace (Fin n → Fin n → 𝕂))

attribute [local instance] matrix_properSpace

/-- **Congruence balls.** Over a complete, proper, ultrametric nontrivially normed field, for every
sufficiently small positive radius `r` the elements within `r` of the identity form a compact
open subgroup, mapped onto the closed ball by `g ↦ g − 1`. -/
theorem exists_congruenceBall :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Ioc 0 r₀, ∃ U : OpenSubgroup (GeneralLinear n 𝕂),
      IsCompact (U : Set (GeneralLinear n 𝕂)) ∧
      (U : Set (GeneralLinear n 𝕂)) = {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r} ∧
      Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
        closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r := by
  obtain ⟨r₀, h0, h⟩ := Langlands.Analysis.unitsCoordinateBall (K := 𝕂)
    (ContinuousLinearEquiv.refl 𝕂 (Matrix (Fin n) (Fin n) 𝕂))
  exact ⟨r₀, h0, h⟩

end Langlands.BaseChange.TwistedLocalDescent
