import Langlands.Automorphic.CuspidalFiniteTensorSlice
import Langlands.Automorphic.CuspidalTensorFunctionalComparison
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerModel
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerPlaces
import Langlands.Representation.Archimedean.MixedSmoothFunctionalExt

/-! # Mixed Whittaker comparison from the actual archimedean tensor slices -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 65000

open scoped Classical TensorProduct Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic Langlands.Global Langlands.Global.FiniteAdelicGL
  Langlands.Global.CuspidalPairFunctionalEquation Langlands.Archimedean
  Langlands.Archimedean.MixedSmooth Langlands.HarmonicAnalysis InfinitePlaceFamily

universe u v

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (hcomm : ∀ g d x, π g (σ d x) = σ d (π g x))

local instance finiteFactorGroup :
    AddCommGroup T.finiteInfiniteDecomposition.finite.toSubmodule :=
  Submodule.addCommGroup _
local instance infiniteFactorGroup (i : Index F) :
    AddCommGroup (T.placeDensityModels.subspace i) :=
  Submodule.addCommGroup _

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
local notation "W" => Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm
local notation "Πf" => MixedSmooth.finiteRepresentation σ π hcomm

variable (j : T.realization.finiteRepresentation.IntertwiningMap
    (MixedSmooth.finiteRepresentation (A := ArchimedeanMatrix F (r + 1)) σ π hcomm))
  (ψ : UnitaryAdditiveCharacter (Adeles F))

local notation "ℱ" => T.allPlaceTensorEquiv.toLinearMap

/-- The remaining local comparison on each actual archimedean tensor
slice holds for the two restrictions to that same slice. -/
def HasArchimedeanWhittakerSliceComparison : Prop :=
  ∀ (ℓ₀ ℓ₁ : W →ₗ[ℂ] ℂ),
    IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ₀ →
    IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ₁ →
      let L₀ := (ℓ₀.comp j.toLinearMap).comp ℱ
      let L₁ := (ℓ₁.comp j.toLinearMap).comp ℱ
      ∀ a b i, (tensorFunctionalMultilinearSlice L₀ a).toLinearMap b i ≠ 0 →
        ∃ c : ℂ, (tensorFunctionalMultilinearSlice L₁ a).toLinearMap b i =
          c • (tensorFunctionalMultilinearSlice L₀ a).toLinearMap b i

omit [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))] in
/-- The actual finite factor contributes a single line on each slice. -/
theorem mixedWhittaker_finiteTensorSlice_proportional
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) (ℓ₀ ℓ₁ : W →ₗ[ℂ] ℂ)
    (h₀ : IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ₀)
    (h₁ : IsMixedWhittakerFunctional (r := r) ψ.complex σ π hcomm ℓ₁)
    (b : ∀ i : Index F, T.placeDensityModels.subspace i)
    (hne : tensorFunctionalLinearSlice ((ℓ₀.comp j.toLinearMap).comp ℱ) b ≠ 0) :
    ∃ c : ℂ, tensorFunctionalLinearSlice ((ℓ₁.comp j.toLinearMap).comp ℱ) b =
      c • tensorFunctionalLinearSlice ((ℓ₀.comp j.toLinearMap).comp ℱ) b := by
  let A := T.finiteInfiniteDecomposition
  let ρ := A.finite.toRepresentation
  let q := j.comp (T.finiteTensorSlice (PiTensorProduct.tprod ℂ b))
  let ψp := canonicalFiniteAdditiveComponent ψ hdiag
  have hψp := isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hdiag
  have hq (d : FiniteAdelicGL F (r + 1)) (a : A.finite.toSubmodule) :
      q (ρ d a) = Πf d (q a) :=
    Representation.IntertwiningMap.isIntertwining _ _ q d a
  have hq₀ := mixedWhittaker_hasComponents σ π hcomm ψ ℓ₀ h₀ ρ q.toLinearMap hq ψp hψp
  have hq₁ := mixedWhittaker_hasComponents σ π hcomm ψ ℓ₁ h₁ ρ q.toLinearMap hq ψp hψp
  exact finiteAdelicWhittakerMultiplicityOne ρ A.admissible A.irreducible ψp
    (ℓ₀.comp q.toLinearMap) (ℓ₁.comp q.toLinearMap) hne hq₀ hq₁

/-- The finite tensor comparison, the archimedean slice comparisons and
the dense original carrier imply uniqueness of mixed Whittaker functionals. -/
theorem mixedWhittakerUniqueness_of_archimedeanSlices
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1)
    (s : T.Space →ₗ[ℂ] Langlands.Archimedean.smoothVectors I π)
    (hs : ∀ w, (j w).val = s w)
    (hd : DenseFixedImages (A := ArchimedeanMatrix F (r + 1))
      T.realization.finiteRepresentation σ π s)
    (harch : HasArchimedeanWhittakerSliceComparison T σ π hcomm j ψ) :
    MixedWhittakerUniqueness (r := r) ψ.complex σ π hcomm := by
  intro ℓ₀ ℓ₁ h₀ h₁ hne
  let L₀ := ℓ₀.comp j.toLinearMap
  let L₁ := ℓ₁.comp j.toLinearMap
  have hL₀ : L₀ ≠ 0 :=
    functional_source_ne_zero T.realization.finiteRepresentation σ π hcomm j s hs hd ℓ₀ h₀.1 hne
  have h : T.HaveProportionalTensorSlices L₀ L₁ :=
    ⟨mixedWhittaker_finiteTensorSlice_proportional T σ π hcomm j ψ hdiag ℓ₀ ℓ₁ h₀ h₁,
      harch ℓ₀ ℓ₁ h₀ h₁⟩
  obtain ⟨c, hc⟩ := T.proportional_of_tensorSlices L₀ L₁ hL₀ h
  exact ⟨c, functional_eq_smul_of_source_values T.realization.finiteRepresentation σ π hcomm
    j s hs hd ℓ₀ ℓ₁ h₀.1 h₁.1 c hc⟩

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
