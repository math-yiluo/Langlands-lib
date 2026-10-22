import Langlands.Global.ArchimedeanLieAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine smooth archimedean directional differentiation

The derivative is taken in the real matrix space in the direction `g * X`.
The coordinate expression need only be smooth on the open set of units.
-/

noncomputable section
universe u
open scoped Classical Manifold ContDiff Matrix.Norms.Operator
open Set Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The global units chart, whose target is the open set of invertible matrices. -/
def unitsChart : OpenPartialHomeomorph (ArchimedeanGL K n) (ArchimedeanMatrix K n) :=
  Units.isOpenEmbedding_val.toOpenPartialHomeomorph Units.val

/-- The coordinate expression is only asserted smooth near invertible matrices. -/
def coordinateExtension (f : SmoothFunctions K n) : ArchimedeanMatrix K n → ℂ :=
  fun a => f.val ((archimedeanGLCoordinates K n).symm ((unitsChart K n).symm a))

@[simp]
theorem coordinateExtension_apply (f : SmoothFunctions K n) (g : ArchimedeanGL K n) :
    coordinateExtension K n f (g : ArchimedeanMatrix K n) =
      f.val ((archimedeanGLCoordinates K n).symm g) := by
  simp only [coordinateExtension, unitsChart,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

theorem coordinateExtension_contDiffOn (f : SmoothFunctions K n) :
    ContDiffOn ℝ ∞ (coordinateExtension K n f)
      (Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) := by
  exact (f.property.comp_contMDiffOn
    (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ, ArchimedeanMatrix K n))
      Units.isOpenEmbedding_val)).contDiffOn

theorem coordinateExtension_contDiffAt (f : SmoothFunctions K n) (g : ArchimedeanGL K n) :
    ContDiffAt ℝ ∞ (coordinateExtension K n f) (g : ArchimedeanMatrix K n) :=
  (coordinateExtension_contDiffOn K n f).contDiffAt
    (Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨g, rfl⟩)

/-- Pointwise derivative in the left-invariant matrix direction `g * X`. -/
def directionalValue (X : RealLieAlgebra K n) (f : SmoothFunctions K n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) : ℂ :=
  fderiv ℝ (coordinateExtension K n f)
    (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)
    ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
      realLieAlgebraToMatrix K n X)

theorem directionalValue_mem (X : RealLieAlgebra K n) (f : SmoothFunctions K n) :
    directionalValue K n X f ∈ smoothFunctions K n := by
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ _
  intro g
  have h := ((coordinateExtension_contDiffAt K n f g).fderiv_right
    (m := ∞) (by simp)).clm_apply
      (contDiffAt_id.mul (contDiffAt_const (c := realLieAlgebraToMatrix K n X)))
  have hcomp := h.comp_contMDiffAt
    (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) g)
  simpa only [Function.comp_def, directionalValue,
    ContinuousMulEquiv.apply_symm_apply] using! hcomp

/-- Differentiation in one real matrix direction, as a complex-linear endomorphism. -/
def smoothDifferential (X : RealLieAlgebra K n) :
    Module.End ℂ (SmoothFunctions K n) where
  toFun f := ⟨directionalValue K n X f, directionalValue_mem K n X f⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    change fderiv ℝ (coordinateExtension K n f + coordinateExtension K n h)
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) _ = _
    rw [fderiv_add
      ((coordinateExtension_contDiffAt K n f _).differentiableAt (by simp))
      ((coordinateExtension_contDiffAt K n h _).differentiableAt (by simp))]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext g
    change fderiv ℝ (c • coordinateExtension K n f)
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) _ = _
    rw [fderiv_const_smul
      ((coordinateExtension_contDiffAt K n f _).differentiableAt (by simp))]
    rfl

@[simp]
theorem smoothDifferential_apply (X : RealLieAlgebra K n) (f : SmoothFunctions K n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (smoothDifferential K n X f).val g =
      fderiv ℝ (coordinateExtension K n f)
        (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n X) := rfl

/-- The direction depends real-linearly on the genuine matrix Lie algebra. -/
def realSmoothDifferential :
    RealLieAlgebra K n →ₗ[ℝ] Module.End ℂ (SmoothFunctions K n) where
  toFun := smoothDifferential K n
  map_add' X Y := by
    ext f g
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, smoothDifferential_apply,
      map_add, mul_add]
  map_smul' c X := by
    ext f g
    change _ = c • (smoothDifferential K n X f).val g
    simp only [smoothDifferential_apply, map_smul, mul_smul_comm]

/-- An ambient extension agreeing on invertible matrices gives the same derivative.
No global smoothness hypothesis on the extension is required. -/
theorem smoothDifferential_eq_of_extension (X : RealLieAlgebra K n)
    (f : SmoothFunctions K n) (F : ArchimedeanMatrix K n → ℂ)
    (hF : ∀ h : ArchimedeanGL K n,
      F (h : ArchimedeanMatrix K n) = f.val ((archimedeanGLCoordinates K n).symm h))
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (smoothDifferential K n X f).val g =
      fderiv ℝ F (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)
        ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
          realLieAlgebraToMatrix K n X) := by
  have heq : coordinateExtension K n f =ᶠ[𝓝
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)] F := by
    filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds
      (show (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) ∈
        Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)
        from ⟨_, rfl⟩)] with a ha
    obtain ⟨h, rfl⟩ := ha
    rw [coordinateExtension_apply, hF]
  rw [smoothDifferential_apply, heq.fderiv_eq]

end Langlands.Global.ArchimedeanGL
