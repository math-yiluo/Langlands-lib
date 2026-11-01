import Langlands.Global.ArchimedeanSmoothAdjointCoefficients
import Langlands.Global.ArchimedeanNormedDerivativeCoordinates
import Langlands.Analysis.CompactParameterSmoothness
import Langlands.Global.ArchimedeanCovarianceProof

/-! # Smooth compact coordinates of actual right-translation orbits -/

noncomputable section
universe u
open scoped Classical Topology BigOperators Manifold ContDiff Matrix.Norms.Operator
open Topology TopologicalSpace Set
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The open domain of the global units chart. -/
def matrixUnitDomain : Set (ArchimedeanMatrix K n) :=
  Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)

theorem isOpen_matrixUnitDomain : IsOpen (matrixUnitDomain K n) :=
  Units.isOpenEmbedding_val.isOpen_range

/-- The genuine positive right-translation orbit in the derivative topology. -/
def derivativeRightOrbit (f : DerivativeSmoothFunctions K n)
    (g : InfiniteAdelicGL K n) : DerivativeSmoothFunctions K n :=
  (DerivativeSmoothFunctions.toSmooth K n).symm
    (smoothRightAction K n g (DerivativeSmoothFunctions.toSmooth K n f))

/-- The orbit expressed in the single ambient matrix chart. -/
def matrixRightOrbit (f : DerivativeSmoothFunctions K n)
    (y : ArchimedeanMatrix K n) : DerivativeSmoothFunctions K n :=
  derivativeRightOrbit K n f
    ((archimedeanGLCoordinates K n).symm ((unitsChart K n).symm y))

theorem matrixRightOrbit_apply (f : DerivativeSmoothFunctions K n)
    (g : ArchimedeanGL K n) :
    matrixRightOrbit K n f (g : ArchimedeanMatrix K n) =
      derivativeRightOrbit K n f ((archimedeanGLCoordinates K n).symm g) := by
  simp only [matrixRightOrbit, unitsChart,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

theorem derivative_rightAction_of_covariance
    (g : InfiniteAdelicGL K n) (a : EnvelopingAlgebra K n) (f : SmoothFunctions K n) :
    envelopingAction K n a (smoothRightAction K n g f) =
      smoothRightAction K n g (envelopingAction K n (envelopingConjugation K n g⁻¹ a) f) := by
  have h := envelopingRightCovariance K n g (envelopingConjugation K n g⁻¹ a) f
  rw [envelopingConjugation_inv, AlgEquiv.apply_symm_apply] at h
  exact h.symm

private theorem envelopingAction_sum_smul_apply (m : ℕ)
    (b : Fin m → EnvelopingAlgebra K n) (c : Fin m → ℂ)
    (f : SmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (envelopingAction K n (∑ i, c i • b i) f).val x =
      ∑ i, c i * (envelopingAction K n (b i) f).val x := by
  simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply]

private def jointOrbitExpansion (m : ℕ) (b : Fin m → EnvelopingAlgebra K n)
    (c : Fin m → SmoothFunctions K n) (f : DerivativeSmoothFunctions K n)
    (p : ArchimedeanMatrix K n × ArchimedeanMatrix K n) : ℂ :=
  ∑ i, coordinateExtension K n (smoothFunctionInv K n (c i)) p.1 *
    coordinateExtension K n
      (envelopingAction K n (b i) (DerivativeSmoothFunctions.toSmooth K n f))
      (p.2 * p.1)

private theorem jointOrbitExpansion_contDiffOn
    (m : ℕ) (b : Fin m → EnvelopingAlgebra K n)
    (c : Fin m → SmoothFunctions K n) (f : DerivativeSmoothFunctions K n) :
    ContDiffOn ℝ ∞ (jointOrbitExpansion K n m b c f)
      (matrixUnitDomain K n ×ˢ matrixUnitDomain K n) := by
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.mul
  · exact (coordinateExtension_contDiffOn K n _).comp contDiffOn_fst
      (fun p hp => hp.1)
  · apply (coordinateExtension_contDiffOn K n _).comp
      (contDiffOn_snd.mul contDiffOn_fst)
    intro p hp
    obtain ⟨g, hg⟩ := hp.1
    obtain ⟨h, hh⟩ := hp.2
    exact ⟨h * g, by simp only [Units.val_mul, hg, hh]⟩

/-- The actual derivative orbit, with both variables in ambient matrix coordinates. -/
def matrixDerivativeRightOrbitValue (f : DerivativeSmoothFunctions K n)
    (a : EnvelopingAlgebra K n)
    (p : ArchimedeanMatrix K n × ArchimedeanMatrix K n) : ℂ :=
  coordinateExtension K n
    (envelopingAction K n a
      (DerivativeSmoothFunctions.toSmooth K n (matrixRightOrbit K n f p.1))) p.2

theorem matrixDerivativeRightOrbitValue_contDiffOn
    (f : DerivativeSmoothFunctions K n) (a : EnvelopingAlgebra K n) :
    ContDiffOn ℝ ∞ (matrixDerivativeRightOrbitValue K n f a)
      (matrixUnitDomain K n ×ˢ matrixUnitDomain K n) := by
  obtain ⟨m, b, c, hc⟩ := envelopingConjugationSmoothCoefficients K n a
  apply (jointOrbitExpansion_contDiffOn K n m b c f).congr
  intro p hp
  obtain ⟨g, hg⟩ := hp.1
  obtain ⟨x, hx⟩ := hp.2
  rcases p with ⟨y, z⟩
  dsimp only at hg hx
  subst y
  subst z
  simp only [matrixDerivativeRightOrbitValue, matrixRightOrbit_apply,
    coordinateExtension_apply]
  change (envelopingAction K n a (smoothRightAction K n
    ((archimedeanGLCoordinates K n).symm g)
    (DerivativeSmoothFunctions.toSmooth K n f))).val
      ((archimedeanGLCoordinates K n).symm x) = _
  rw [derivative_rightAction_of_covariance, smoothRightAction_apply, hc,
    envelopingAction_sum_smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (c i).val _ * _ =
    coordinateExtension K n (smoothFunctionInv K n (c i)) (g : ArchimedeanMatrix K n) *
      coordinateExtension K n _ (x.val * g.val)
  rw [← Units.val_mul, coordinateExtension_apply, coordinateExtension_apply]
  simp only [smoothFunctionInv, map_mul]

/-- Each genuine enveloping derivative, restricted to any compact set, is a
smooth normed-space-valued function of the translating matrix. -/
theorem matrixRightOrbit_normedDerivative_contDiffOn
    (f : DerivativeSmoothFunctions K n) (a : EnvelopingAlgebra K n)
    (s : Compacts (InfiniteAdelicGL K n)) :
    ContDiffOn ℝ ∞
      (fun y => DerivativeSmoothFunctions.normedDerivativeCoordinates K n
        (matrixRightOrbit K n f y) (a, s))
      (matrixUnitDomain K n) := by
  obtain ⟨m, b, c, hc⟩ := envelopingConjugationSmoothCoefficients K n a
  let j : C(s, ArchimedeanMatrix K n) :=
    ⟨fun x => (archimedeanGLCoordinates K n x.val).val,
      Units.continuous_val.comp
        ((archimedeanGLCoordinates K n).continuous.comp continuous_subtype_val)⟩
  apply Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint j
    (isOpen_matrixUnitDomain K n) (isOpen_matrixUnitDomain K n)
    (fun x => ⟨archimedeanGLCoordinates K n x.val, rfl⟩)
    (jointOrbitExpansion_contDiffOn K n m b c f)
  intro y hy x
  obtain ⟨g, rfl⟩ := hy
  rw [matrixRightOrbit_apply]
  change (envelopingAction K n a (smoothRightAction K n
    ((archimedeanGLCoordinates K n).symm g)
    (DerivativeSmoothFunctions.toSmooth K n f))).val x.val = _
  rw [derivative_rightAction_of_covariance, smoothRightAction_apply, hc,
    envelopingAction_sum_smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (c i).val _ * _ =
    coordinateExtension K n (smoothFunctionInv K n (c i)) (g : ArchimedeanMatrix K n) *
      coordinateExtension K n _ ((archimedeanGLCoordinates K n x.val).val * g.val)
  rw [← Units.val_mul, coordinateExtension_apply, coordinateExtension_apply]
  simp only [smoothFunctionInv, map_mul, ContinuousMulEquiv.symm_apply_apply]

/-- An arbitrary continuous scalar functional gives a smooth scalar coefficient
on the actual open matrix chart. -/
theorem matrixRightOrbit_scalar_contDiffOn
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (f : DerivativeSmoothFunctions K n) :
    ContDiffOn ℝ ∞ (fun y => ℓ (matrixRightOrbit K n f y))
      (matrixUnitDomain K n) := by
  apply DerivativeSmoothFunctions.contDiffOn_scalar_of_normedDerivativeCoordinates K n ℓ
  intro i
  exact matrixRightOrbit_normedDerivative_contDiffOn K n f i.1 i.2

/-- The actual scalar coefficient as a genuine smooth function. -/
def smoothOrbitCoefficient
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (f : DerivativeSmoothFunctions K n) : SmoothFunctions K n :=
  ⟨fun g => ℓ (derivativeRightOrbit K n f g), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ _
    have h := (matrixRightOrbit_scalar_contDiffOn K n ℓ f).contMDiffOn.comp_contMDiff
      (Units.contMDiff_val (𝕜 := ℝ) (n := ∞))
      (fun g => ⟨g, rfl⟩)
    simpa only [Function.comp_def, matrixRightOrbit_apply,
      ContinuousMulEquiv.symm_apply_apply] using h⟩

@[simp]
theorem smoothOrbitCoefficient_apply
    (ℓ : DerivativeSmoothFunctions K n →L[ℂ] ℂ)
    (f : DerivativeSmoothFunctions K n) (g : InfiniteAdelicGL K n) :
    (smoothOrbitCoefficient K n ℓ f).val g = ℓ (derivativeRightOrbit K n f g) := rfl

end Langlands.Global.ArchimedeanGL
