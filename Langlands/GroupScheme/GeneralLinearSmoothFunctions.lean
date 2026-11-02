import Langlands.GroupScheme.AffinePointSmoothFunctions
import Langlands.GroupScheme.GeneralLinearCoordinateSmooth
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.ArchimedeanGL

/-! # Actual general-linear plot-smooth and archimedean smooth functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.GroupScheme.GeneralLinear

set_option backward.isDefEq.respectTransparency false

variable (n : Type) [Fintype n] [DecidableEq n]
  (R : CommRingCat.{u}) (A : CommAlgCat.{u} R)
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  (e : A ≃+* B)

local instance smoothFunctionsMatrixComplete : CompleteSpace (Matrix n n B) :=
  inferInstanceAs (CompleteSpace (n → n → B))

/-- A coefficient ring equivalence makes the actual coefficient-coordinate
homomorphism a group equivalence. -/
def coefficientCoordinatesEquiv :
    (groupScheme n R).affinePoints A ≃* GL n B where
  toFun := coefficientCoordinates n R A e.toRingHom
  invFun g := (affinePointsEquiv n R A).symm
    (Matrix.GeneralLinearGroup.map e.symm.toRingHom g)
  left_inv p := by
    apply (affinePointsEquiv n R A).injective
    change (affinePointsEquiv n R A)
      ((affinePointsEquiv n R A).symm
        (Matrix.GeneralLinearGroup.map e.symm.toRingHom
          (Matrix.GeneralLinearGroup.map e.toRingHom (affinePointsEquiv n R A p)))) = _
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact e.symm_apply_apply _
  right_inv g := by
    change Matrix.GeneralLinearGroup.map e.toRingHom
      ((affinePointsEquiv n R A)
        ((affinePointsEquiv n R A).symm
          (Matrix.GeneralLinearGroup.map e.symm.toRingHom g))) = g
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact e.apply_symm_apply _
  map_mul' := map_mul _

omit [NormedAlgebra ℝ B] [CompleteSpace B] in
@[simp]
theorem coefficientCoordinatesEquiv_apply (p : (groupScheme n R).affinePoints A) :
    coefficientCoordinatesEquiv n R A e p =
      coefficientCoordinates n R A e.toRingHom p := rfl

/-- For general-linear points, the all-family condition recovers the existing
matrix-units manifold condition whenever the coefficient map is an equivalence. -/
theorem isPlotSmooth_iff_contMDiff (f : (groupScheme n R).affinePoints A → ℂ) :
    (groupScheme n R).IsPlotSmooth A e.toRingHom f ↔
      ContMDiff 𝓘(ℝ, Matrix n n B) 𝓘(ℝ, ℂ) ∞
        (fun x : GL n B => f ((coefficientCoordinatesEquiv n R A e).symm x)) := by
  constructor
  · intro hf
    have hp : (groupScheme n R).CoordinateSmooth A e.toRingHom
        𝓘(ℝ, Matrix n n B) (coefficientCoordinatesEquiv n R A e).symm := by
      apply (coordinateSmooth_iff_contMDiff n R A e.toRingHom
        𝓘(ℝ, Matrix n n B) _).mpr
      simp only [← coefficientCoordinatesEquiv_apply, MulEquiv.apply_symm_apply]
      exact contMDiff_id
    exact hf (Matrix n n B) (GL n B) _ hp
  · intro hf E _ _ M _ _ p hp
    have hs := (coordinateSmooth_iff_contMDiff n R A e.toRingHom 𝓘(ℝ, E) p).mp hp
    have h := hf.comp hs
    simpa only [Function.comp_def, ← coefficientCoordinatesEquiv_apply,
      MulEquiv.symm_apply_apply] using h

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.Global.GeneralLinearGroupPoints

open NumberField

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance generalLinearIsAffine :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- Plot-smooth functions on actual infinite adelic points are exactly the
original archimedean smooth functions under the existing point comparison. -/
theorem isPlotSmooth_iff_mem_smoothFunctions
    (f : InfiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) → ℂ) :
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).IsPlotSmooth
      (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom f ↔
    (fun x => f ((infiniteHomeomorph F n).symm x)) ∈ ArchimedeanGL.smoothFunctions F n := by
  rw [GroupScheme.GeneralLinear.isPlotSmooth_iff_contMDiff (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (InfiniteAdeleRing F)) (InfiniteAdeleRing.ringEquiv_mixedSpace F)]
  rfl

/-- The actual-point comparison restricts to a complex linear equivalence
with the original archimedean smooth-function space. -/
def plotSmoothGeneralLinearEquiv :
    ↥((GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).plotSmoothFunctions
      (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)
      ≃ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n where
  toFun f := ⟨fun x => f.val ((infiniteHomeomorph F n).symm x),
    (isPlotSmooth_iff_mem_smoothFunctions F n f.val).mp f.property⟩
  invFun f := ⟨fun x => f.val (infiniteHomeomorph F n x), by
    change (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).IsPlotSmooth
      (CommAlgCat.of F (InfiniteAdeleRing F)) (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
      (fun x => f.val (infiniteHomeomorph F n x))
    apply (isPlotSmooth_iff_mem_smoothFunctions F n _).mpr
    simpa only [ContinuousMulEquiv.apply_symm_apply] using f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    exact congrArg f.val ((infiniteHomeomorph F n).symm_apply_apply x)
  right_inv f := by
    apply Subtype.ext
    funext x
    exact congrArg f.val ((infiniteHomeomorph F n).apply_symm_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem plotSmoothGeneralLinearEquiv_apply
    (f : ↥((GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).plotSmoothFunctions
      (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom))
    (x : InfiniteAdelicGL F n) :
    (plotSmoothGeneralLinearEquiv F n f).val x =
      f.val ((infiniteHomeomorph F n).symm x) := rfl

/-- The comparison preserves the original positive right-translation action. -/
theorem plotSmoothGeneralLinearEquiv_rightAction
    (g : InfiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (f : ↥((GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).plotSmoothFunctions
      (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)) :
    plotSmoothGeneralLinearEquiv F n
      ((GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).plotSmoothRightAction
        (CommAlgCat.of F (InfiniteAdeleRing F))
        (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom g f) =
    ArchimedeanGL.smoothRightAction F n (infiniteHomeomorph F n g)
      (plotSmoothGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  funext x
  change f.val ((infiniteHomeomorph F n).symm x * g) =
    f.val ((infiniteHomeomorph F n).symm (x * infiniteHomeomorph F n g))
  rw [map_mul, ContinuousMulEquiv.symm_apply_apply]

end Langlands.Global.GeneralLinearGroupPoints
