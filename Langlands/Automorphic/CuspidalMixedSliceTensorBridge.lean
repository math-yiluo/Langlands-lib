import Langlands.Automorphic.CuspidalArchimedeanSliceTensor
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerTensor

/-! # Converting the algebraic slice comparison to tensor coordinates -/

noncomputable section
open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global RankinSelbergGlobal RankinSelbergGlobal.ArchimedeanWhittakerRegularity
open Langlands.Archimedean MixedSmooth
open Langlands.HarmonicAnalysis InfinitePlaceFamily
universe u v
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))
  (j : T.realization.finiteRepresentation.IntertwiningMap
    (MixedSmooth.finiteRepresentation (A := ArchimedeanMatrix F (r + 1)) σ π hcomm))
  (ψ : UnitaryAdditiveCharacter (Adeles F))

local notation "W" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm

/-- A comparison of restrictions along the algebraic slice map gives the
archimedean slot condition of the tensor argument. -/
theorem hasArchimedeanWhittakerSliceComparison_of_algebraicSlices
    (h : ∀ (i : Index F) (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
      (b : ∀ j, T.placeDensityModels.subspace j) (ℓ₀ ℓ₁ : W →ₗ[ℂ] ℂ),
      IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ₀ →
      IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ₁ →
      let L := j.toLinearMap.comp (T.placeTensorSlice i a b)
      ℓ₀.comp L ≠ 0 → ∃ c : ℂ, ℓ₁.comp L = c • ℓ₀.comp L) :
    HasArchimedeanWhittakerSliceComparison T σ π hcomm j ψ := by
  intro ℓ₀ ℓ₁ h₀ h₁ L₀ L₁ a b i hn
  let S := T.placeTensorSlice i a b
  have h₀eq :=
    (T.tensorFunctionalMultilinearSlice_eq_comp_placeTensorSlice (ℓ₀.comp j.toLinearMap) a b i).trans
      (LinearMap.comp_assoc S j.toLinearMap ℓ₀)
  have h₁eq :=
    (T.tensorFunctionalMultilinearSlice_eq_comp_placeTensorSlice (ℓ₁.comp j.toLinearMap) a b i).trans
      (LinearMap.comp_assoc S j.toLinearMap ℓ₁)
  have hn' : ℓ₀.comp (j.toLinearMap.comp (T.placeTensorSlice i a b)) ≠ 0 :=
    fun hzero => hn (h₀eq.trans hzero)
  let hc := h i a b ℓ₀ ℓ₁ h₀ h₁ hn'
  let c := Classical.choose hc
  exact ⟨c, h₁eq.trans ((Classical.choose_spec hc).trans (congrArg (c • ·) h₀eq.symm))⟩

end Langlands.Automorphic
