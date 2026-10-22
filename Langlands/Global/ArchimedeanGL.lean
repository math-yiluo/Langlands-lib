import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Real manifold coordinates for archimedean matrix groups

The mixed real/complex space supplies the Banach algebra norm. The normalized
product norm on the infinite adele ring is not used as a Banach algebra norm.
-/

noncomputable section

universe u

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable (K : Type u) [Field K]

theorem continuous_infiniteAdeleCoordinates :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  exact (continuous_pi fun v =>
    (isometryEquivRealOfIsReal v.property).continuous.comp (continuous_apply v.val)).prodMk
      (continuous_pi fun v =>
        (isometryEquivComplexOfIsComplex v.property).continuous.comp (continuous_apply v.val))

theorem infiniteAdeleCoordinates_symm_real
    (y : mixedEmbedding.mixedSpace K) (v : InfinitePlace K) (hv : IsReal v) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v =
      (ringEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
  apply (ringEquivRealOfIsReal hv).injective
  have h := congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
  rw [RingEquiv.apply_symm_apply]
  exact h

theorem infiniteAdeleCoordinates_symm_complex
    (y : mixedEmbedding.mixedSpace K) (v : InfinitePlace K) (hv : IsComplex v) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v =
      (ringEquivComplexOfIsComplex hv).symm (y.2 ⟨v, hv⟩) := by
  apply (ringEquivComplexOfIsComplex hv).injective
  have h := congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
  rw [RingEquiv.apply_symm_apply]
  exact h

theorem continuous_infiniteAdeleCoordinates_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  change Continuous (fun y : mixedEmbedding.mixedSpace K =>
    fun v : InfinitePlace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · simp_rw [infiniteAdeleCoordinates_symm_real K _ v hv]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply (⟨v, hv⟩ : {w : InfinitePlace K // IsReal w})).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.mp hv
    simp_rw [infiniteAdeleCoordinates_symm_complex K _ v hc]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply (⟨v, hc⟩ : {w : InfinitePlace K // IsComplex w})).comp continuous_snd)

/-- The completion-based infinite adeles have their original topology in mixed coordinates. -/
def infiniteAdeleHomeomorph :
    InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K where
  __ := (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv
  continuous_toFun := continuous_infiniteAdeleCoordinates K
  continuous_invFun := continuous_infiniteAdeleCoordinates_symm K

variable (n : ℕ)

/-- The real Banach algebra of matrices over the actual mixed archimedean space. -/
abbrev ArchimedeanMatrix := Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)

/-- Invertible matrices in the actual product of real and complex fields. -/
abbrev ArchimedeanGL := Matrix.GeneralLinearGroup (Fin n) (mixedEmbedding.mixedSpace K)

/-- A continuous multiplicative equivalence from completion coordinates to real manifold
coordinates. The map is entrywise the existing number-field ring equivalence. -/
def archimedeanGLCoordinates :
    Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K) ≃ₜ* ArchimedeanGL K n where
  toFun := Matrix.GeneralLinearGroup.map
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom
  invFun := Matrix.GeneralLinearGroup.map
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom
  left_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply (g i j)
  right_inv g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply (g i j)
  map_mul' := map_mul _
  continuous_toFun := (continuous_infiniteAdeleCoordinates K).generalLinearGroup_map
  continuous_invFun := (continuous_infiniteAdeleCoordinates_symm K).generalLinearGroup_map

@[simp]
theorem archimedeanGLCoordinates_apply
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) (i j : Fin n) :
    archimedeanGLCoordinates K n g i j =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (g i j) := rfl

variable [NumberField K]

namespace ArchimedeanGL

-- The matrix norm and product topology are definitionally compatible, but
-- resolving the units charts needs reduction through the normed-ring instances.
set_option backward.isDefEq.respectTransparency false

/-- Smooth complex-valued functions on the actual completion-based group. Smoothness
is real smoothness, expressed through the constructed mixed coordinates. -/
def smoothFunctions : Submodule ℂ
    (Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K) → ℂ) where
  carrier := {f | ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞
    (fun x : ArchimedeanGL K n => f ((archimedeanGLCoordinates K n).symm x))}
  zero_mem' := contMDiff_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := by
    exact (((ContinuousLinearMap.mul ℝ ℂ) c).contDiff.contMDiff).comp hf

/-- The genuine vector space underlying the smooth-function submodule. -/
abbrev SmoothFunctions := ↥(smoothFunctions K n)

theorem continuous (f : SmoothFunctions K n) : Continuous f.val := by
  have h := f.property.continuous.comp (archimedeanGLCoordinates K n).continuous
  change Continuous (fun x => f.val
    ((archimedeanGLCoordinates K n).symm (archimedeanGLCoordinates K n x))) at h
  simpa only [Function.comp_def, ContinuousMulEquiv.symm_apply_apply] using h

/-- Right translation preserves real smoothness and gives a genuine complex representation. -/
def smoothRightAction : Representation ℂ
    (Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) (SmoothFunctions K n) where
  toFun g :=
    { toFun f := ⟨fun x => f.val (x * g), by
        change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞
          (fun x : ArchimedeanGL K n => f.val ((archimedeanGLCoordinates K n).symm x * g))
        have hg : ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n)
            𝓘(ℝ, ArchimedeanMatrix K n) ∞
            (fun x : ArchimedeanGL K n => x * archimedeanGLCoordinates K n g) :=
          contMDiff_id.mul contMDiff_const
        simpa only [Function.comp_def, map_mul, ContinuousMulEquiv.symm_apply_apply]
          using f.property.comp hg⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    ext f x
    exact congrArg f.val (mul_assoc x g h).symm

@[simp]
theorem smoothRightAction_apply
    (g x : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K))
    (f : SmoothFunctions K n) :
    (smoothRightAction K n g f).val x = f.val (x * g) := rfl

/-- The faithful linear inclusion into actual continuous functions. No assertion about
the stronger smooth-function topology is implicit in this map. -/
def toContinuousMap : SmoothFunctions K n →ₗ[ℂ]
    C(Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K), ℂ) where
  toFun f := ⟨f.val, continuous K n f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toContinuousMap_injective : Function.Injective (toContinuousMap K n) := by
  intro f g h
  apply Subtype.ext
  exact congrArg ContinuousMap.toFun h

end ArchimedeanGL

end Langlands.Global
