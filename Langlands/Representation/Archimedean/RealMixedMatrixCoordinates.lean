import Langlands.Global.ArchimedeanGL
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Langlands.Representation.Archimedean.GeneralLinear

/-! # Real matrix coordinates from the unique archimedean place of the rationals -/

noncomputable section

open NumberField
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

private def rationalRealPlace : {v : InfinitePlace ℚ // v.IsReal} :=
  ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

private theorem rationalComplexPlace_false (v : {v : InfinitePlace ℚ // v.IsComplex}) : False :=
  (InfinitePlace.not_isReal_iff_isComplex.mpr v.property)
    (NumberField.IsTotallyReal.isReal v.val)

/-- Evaluation at the unique real place identifies the rational mixed space with `ℝ`. -/
def rationalMixedSpaceEquiv : mixedEmbedding.mixedSpace ℚ ≃ₐ[ℝ] ℝ where
  toFun a := a.1 rationalRealPlace
  invFun r := (fun _ => r, fun _ => 0)
  left_inv a := by
    apply Prod.ext
    · funext v
      exact congrArg a.1 (Subsingleton.elim _ _)
    · funext v
      exact (rationalComplexPlace_false v).elim
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem rationalMixedSpaceEquiv_apply (a : mixedEmbedding.mixedSpace ℚ) :
    rationalMixedSpaceEquiv a = a.1 rationalRealPlace := rfl

@[simp]
theorem rationalMixedSpaceEquiv_star (a : mixedEmbedding.mixedSpace ℚ) :
    rationalMixedSpaceEquiv (star a) = rationalMixedSpaceEquiv a := rfl

variable (n : ℕ)

local notation "A" => Langlands.Global.ArchimedeanMatrix ℚ n
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "U" => Langlands.Global.ArchimedeanGL ℚ n
local notation "GLR" => Langlands.GeneralLinear n ℝ

/-- Entrywise real coordinates on the rational mixed matrix algebra. -/
def rationalMixedMatrixEquiv : A ≃ₐ[ℝ] M := rationalMixedSpaceEquiv.mapMatrix

/-- The same coordinate comparison in the actual norm topologies. -/
def rationalMixedMatrixCLE : A ≃L[ℝ] M :=
  (rationalMixedMatrixEquiv n).toLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem rationalMixedMatrixCLE_apply (X : A) :
    rationalMixedMatrixCLE n X = rationalMixedMatrixEquiv n X := rfl

@[simp]
theorem rationalMixedMatrixCLE_symm_apply (X : M) :
    (rationalMixedMatrixCLE n).symm X = (rationalMixedMatrixEquiv n).symm X := rfl

@[simp]
theorem rationalMixedMatrixEquiv_star (X : A) :
    rationalMixedMatrixEquiv n (star X) = star (rationalMixedMatrixEquiv n X) := by
  ext i j
  rfl

/-- The multiplicative equivalence of the mixed units and the actual real general linear group. -/
def rationalMixedUnitsEquiv : U ≃* GLR :=
  Units.mapEquiv (rationalMixedMatrixEquiv n).toRingEquiv.toMulEquiv

@[simp]
theorem rationalMixedUnitsEquiv_val (g : U) :
    (rationalMixedUnitsEquiv n g : M) = rationalMixedMatrixEquiv n (g : A) := rfl

@[simp]
theorem rationalMixedUnitsEquiv_symm_val (g : GLR) :
    ((rationalMixedUnitsEquiv n).symm g : A) = (rationalMixedMatrixEquiv n).symm (g : M) := rfl

/-- The unit comparison is smooth in the two actual units manifolds. -/
theorem contMDiff_rationalMixedUnitsEquiv :
    ContMDiff 𝓘(ℝ, A) (matrixModel ℝ n) ∞ (rationalMixedUnitsEquiv n) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  change ContMDiff 𝓘(ℝ, A) (matrixModel ℝ n) ∞
    (fun g : U => rationalMixedMatrixCLE n (g : A))
  exact (rationalMixedMatrixCLE n).contDiff.contMDiff.comp Units.contMDiff_val

/-- The inverse unit comparison is smooth in the actual units manifolds. -/
theorem contMDiff_rationalMixedUnitsEquiv_symm :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, A) ∞ (rationalMixedUnitsEquiv n).symm := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  change ContMDiff (matrixModel ℝ n) 𝓘(ℝ, A) ∞
    (fun g : GLR => (rationalMixedMatrixCLE n).symm (g : M))
  exact (rationalMixedMatrixCLE n).symm.contDiff.contMDiff.comp Units.contMDiff_val

end Langlands.Archimedean
