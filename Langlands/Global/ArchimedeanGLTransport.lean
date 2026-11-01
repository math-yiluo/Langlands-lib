import Langlands.Global.ArchimedeanGL
import Langlands.Global.AdelicFunctoriality.Infinite
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Arithmetic transport and real smoothness on archimedean matrix groups -/

noncomputable section
universe uK uL uM

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGLTransport

open NumberField AdelicFunctoriality

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

/-- Actual arithmetic transport in the existing mixed real/complex coordinates. -/
def mixedEquiv (e : K ≃+* L) :
    mixedEmbedding.mixedSpace K ≃+* mixedEmbedding.mixedSpace L :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.trans
    ((infiniteAdeleEquiv e).trans (InfiniteAdeleRing.ringEquiv_mixedSpace L))

theorem continuous_mixedEquiv (e : K ≃+* L) : Continuous (mixedEquiv e) :=
  (continuous_infiniteAdeleCoordinates L).comp
    ((continuous_infiniteAdeleEquiv e).comp (continuous_infiniteAdeleCoordinates_symm K))

theorem continuous_mixedEquiv_symm (e : K ≃+* L) : Continuous (mixedEquiv e).symm :=
  (continuous_infiniteAdeleCoordinates K).comp
    ((continuous_infiniteAdeleEquiv_symm e).comp (continuous_infiniteAdeleCoordinates_symm L))

/-- Arithmetic transport is real linear by additivity and continuity. -/
def mixedRealLinearEquiv (e : K ≃+* L) :
    mixedEmbedding.mixedSpace K ≃L[ℝ] mixedEmbedding.mixedSpace L :=
  (mixedEquiv e).toAddEquiv.toRealLinearEquiv
    (continuous_mixedEquiv e) (continuous_mixedEquiv_symm e)

@[simp] theorem mixedRealLinearEquiv_apply (e : K ≃+* L)
    (x : mixedEmbedding.mixedSpace K) :
    mixedRealLinearEquiv e x = mixedEquiv e x := rfl

/-- Entrywise arithmetic transport on the actual real matrix model. -/
def matrixRealLinearEquiv (n : ℕ) (e : K ≃+* L) :
    ArchimedeanMatrix K n ≃L[ℝ] ArchimedeanMatrix L n :=
  ((mixedEquiv e).toAddEquiv.mapMatrix).toRealLinearEquiv
    (continuous_pi fun i => continuous_pi fun j =>
      (continuous_mixedEquiv e).comp ((continuous_apply j).comp (continuous_apply i)))
    (continuous_pi fun i => continuous_pi fun j =>
      (continuous_mixedEquiv_symm e).comp ((continuous_apply j).comp (continuous_apply i)))

@[simp] theorem matrixRealLinearEquiv_apply (n : ℕ) (e : K ≃+* L)
    (x : ArchimedeanMatrix K n) (i j : Fin n) :
    matrixRealLinearEquiv n e x i j = mixedEquiv e (x i j) := rfl

-- Reduce the units manifold through the existing normed matrix instances.
set_option backward.isDefEq.respectTransparency false

/-- The actual arithmetic map of matrix units is smooth in the real manifold charts. -/
theorem contMDiff_mixed_map (n : ℕ) (e : K ≃+* L) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ArchimedeanMatrix L n) ∞
      (Matrix.GeneralLinearGroup.map (mixedEquiv e).toRingHom :
        ArchimedeanGL K n → ArchimedeanGL L n) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ArchimedeanMatrix L n) ∞
    (fun g : ArchimedeanGL K n => matrixRealLinearEquiv n e (g : ArchimedeanMatrix K n))
  exact (matrixRealLinearEquiv n e).contDiff.contMDiff.comp Units.contMDiff_val

/-- The arithmetic completion map expressed in the actual mixed manifold charts. -/
theorem coordinates_arithmetic_map (n : ℕ) (e : K ≃+* L)
    (g : ArchimedeanGL K n) :
    archimedeanGLCoordinates L n
        (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom
          ((archimedeanGLCoordinates K n).symm g)) =
      Matrix.GeneralLinearGroup.map (mixedEquiv e).toRingHom g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- Arithmetic transport of completion-based matrices is real smooth in both directions. -/
theorem contMDiff_arithmetic_map (n : ℕ) (e : K ≃+* L) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ArchimedeanMatrix L n) ∞
      (fun g : ArchimedeanGL K n => archimedeanGLCoordinates L n
        (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom
          ((archimedeanGLCoordinates K n).symm g))) := by
  simp_rw [coordinates_arithmetic_map]
  exact contMDiff_mixed_map n e

/-- Precomposition by the actual arithmetic infinite-adele matrix map. -/
def smoothComap (n : ℕ) (e : K ≃+* L) :
    ArchimedeanGL.SmoothFunctions L n →ₗ[ℂ] ArchimedeanGL.SmoothFunctions K n where
  toFun f := ⟨fun g => f.val
    (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g), by
      change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞
        (fun x : ArchimedeanGL K n => f.val
          (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom
            ((archimedeanGLCoordinates K n).symm x)))
      have h := f.property.comp (contMDiff_arithmetic_map n e)
      simpa only [Function.comp_def, ContinuousMulEquiv.symm_apply_apply] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem smoothComap_apply (n : ℕ) (e : K ≃+* L)
    (f : ArchimedeanGL.SmoothFunctions L n)
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    (smoothComap n e f).val g =
      f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) := rfl

@[simp] theorem smoothComap_refl (n : ℕ) (f : ArchimedeanGL.SmoothFunctions K n) :
    smoothComap n (RingEquiv.refl K) f = f := by
  apply Subtype.ext
  funext g
  change f.val (Matrix.GeneralLinearGroup.map
    (infiniteAdeleEquiv (RingEquiv.refl K)).toRingHom g) = f.val g
  rw [infiniteAdeleEquiv_refl]
  rfl

/-- Pullback reverses the arithmetic composition order. -/
theorem smoothComap_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M)
    (f : ArchimedeanGL.SmoothFunctions M n) :
    smoothComap n (e.trans a) f = smoothComap n e (smoothComap n a f) := by
  apply Subtype.ext
  funext g
  change f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv (e.trans a)).toRingHom g) =
    f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv a).toRingHom
      (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g))
  rw [infiniteAdeleEquiv_trans]
  rfl

@[simp] theorem smoothComap_symm_apply (n : ℕ) (e : K ≃+* L)
    (f : ArchimedeanGL.SmoothFunctions L n) :
    smoothComap n e.symm (smoothComap n e f) = f := by
  rw [← smoothComap_trans]
  simp only [RingEquiv.symm_trans_self, smoothComap_refl]

@[simp] theorem smoothComap_apply_symm (n : ℕ) (e : K ≃+* L)
    (f : ArchimedeanGL.SmoothFunctions K n) :
    smoothComap n e (smoothComap n e.symm f) = f := by
  rw [← smoothComap_trans]
  simp only [RingEquiv.self_trans_symm, smoothComap_refl]

/-- The genuine complex-linear pullback equivalence on the existing smooth functions. -/
def smoothEquiv (n : ℕ) (e : K ≃+* L) :
    ArchimedeanGL.SmoothFunctions L n ≃ₗ[ℂ] ArchimedeanGL.SmoothFunctions K n where
  __ := smoothComap n e
  invFun := smoothComap n e.symm
  left_inv := smoothComap_symm_apply n e
  right_inv := smoothComap_apply_symm n e

@[simp] theorem smoothEquiv_apply (n : ℕ) (e : K ≃+* L)
    (f : ArchimedeanGL.SmoothFunctions L n)
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    (smoothEquiv n e f).val g =
      f.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) := rfl

/-- Pullback intertwines right translation through the actual arithmetic matrix map. -/
theorem smoothComap_rightAction (n : ℕ) (e : K ≃+* L)
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))
    (f : ArchimedeanGL.SmoothFunctions L n) :
    smoothComap n e
        (ArchimedeanGL.smoothRightAction L n
          (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) f) =
      ArchimedeanGL.smoothRightAction K n g (smoothComap n e f) := by
  apply Subtype.ext
  funext x
  exact congrArg f.val (map_mul
    (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom) x g).symm

end Langlands.Global.ArchimedeanGLTransport
