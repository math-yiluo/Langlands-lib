import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerTensor
import Langlands.Global.HeckeDeterminantLocalConstancy

/-! # The mixed tensor comparison for a standard complex character -/

noncomputable section
open NumberField
open scoped Classical Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global RankinSelbergGlobal RankinSelbergGlobal.ArchimedeanWhittakerRegularity
open Langlands.Archimedean MixedSmooth Langlands.HarmonicAnalysis
universe u v

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup
  finiteAdelicGL_nonarchimedeanGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (cm : ∀ g d x, π g (σ d x) = σ d (π g x))
  (j : T.realization.finiteRepresentation.IntertwiningMap
    (MixedSmooth.finiteRepresentation (A := ArchimedeanMatrix F (r + 1)) σ π cm))
  (s : T.Space →ₗ[ℂ] Langlands.Archimedean.smoothVectors 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π)

/-- A standard complex character has the unitary additive form used by the
all-place mixed Whittaker tensor comparison. -/
theorem mixedWhittakerUniqueness_of_standardCharacter
    (hs : ∀ v, (j v).val = s v)
    (hd : DenseFixedImages (A := ArchimedeanMatrix F (r + 1)) T.realization.finiteRepresentation σ π s)
    (harch : ∀ η : UnitaryAdditiveCharacter (Adeles F), IsStandardAdditiveCharacter F η.complex →
      HasArchimedeanWhittakerSliceComparison T σ π cm j η)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) :
    MixedWhittakerUniqueness (r := r) ψ σ π cm := by
  let ψ₀ := UnitaryAdditiveCharacter.ofComplex ψ hψ.1 hψ.2.1 hψ.2.2.2
  have hdiag (x : F) : ψ₀ (diagonal F x) = 1 := Subtype.ext (hψ.2.2.1 x)
  exact mixedWhittakerUniqueness_of_archimedeanSlices T σ π cm j ψ₀ hdiag s hs hd (harch ψ₀ hψ)

end Langlands.Automorphic
