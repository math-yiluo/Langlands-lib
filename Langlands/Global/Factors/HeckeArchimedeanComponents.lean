import Langlands.Global.Factors.HeckeLocalNontrivial
import Langlands.LocalFactor.ComplexCharacterExistence

/-! # Actual archimedean components and local presentation data -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField
open Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean

variable {K : Type u} [Field K]

/-- The local quasicharacter on real units obtained through the chosen completion equivalence. -/
def realCompletionCharacter {v : InfinitePlace K} (hv : v.IsReal)
    (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) : ℝˣ →ₜ* ℂˣ :=
  η.comp
    { toMonoidHom := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom
      continuous_toFun :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.units_map _ }

/-- The local quasicharacter on complex units obtained through the chosen completion equivalence. -/
def complexCompletionCharacter {v : InfinitePlace K} (hv : v.IsComplex)
    (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) : ℂˣ →ₜ* ℂˣ :=
  η.comp
    { toMonoidHom := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom
      continuous_toFun :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous.units_map _ }

/-- Polar data presenting the given character at an actual real completion. -/
def realCompletionCharacterData {v : InfinitePlace K} (hv : v.IsReal)
    (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) : RealCharacterData :=
  realCharacterData (realCompletionCharacter hv η)

/-- Polar data presenting the given character at an actual complex completion. -/
def complexCompletionCharacterData {v : InfinitePlace K} (hv : v.IsComplex)
    (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) : ComplexCharacterData :=
  complexCharacterData (complexCompletionCharacter hv η)

theorem isRealCharacterPresentation_realCompletionCharacterData
    {v : InfinitePlace K} (hv : v.IsReal) (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) :
    IsRealCharacterPresentation hv η (realCompletionCharacterData hv η) := by
  intro x
  change η (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom
    (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMonoidHom x)) = η x
  congr 1
  apply Units.ext
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm_apply_apply _

theorem isComplexCharacterPresentation_complexCompletionCharacterData
    {v : InfinitePlace K} (hv : v.IsComplex) (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) :
    IsComplexCharacterPresentation hv η (complexCompletionCharacterData hv η) := by
  intro x
  change η (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toMonoidHom x)) = η x
  congr 1
  apply Units.ext
  exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm_apply_apply _

variable [NumberField K]

/-- The actual infinite restriction, bundled when its nontriviality is proved. -/
def infiniteAdditiveComponent
    (ψ : UnitaryAdditiveCharacter (Adeles K)) (v : InfinitePlace K)
    (h : infiniteAdditiveRestriction ψ v ≠ 1) :
    UnitaryAdditiveCharacter (InfiniteCompletion K v) where
  toAddChar := infiniteAdditiveRestriction ψ v
  continuous_toFun := continuous_infiniteAdditiveRestriction ψ v
  nontrivial := h

/-- Transport the actual nontrivial real-completion restriction to the real field. -/
def realCompletionAdditiveCharacter
    (ψ : UnitaryAdditiveCharacter (Adeles K)) {v : InfinitePlace K} (hv : v.IsReal)
    (h : infiniteAdditiveRestriction ψ v ≠ 1) : UnitaryAdditiveCharacter ℝ :=
  (infiniteAdditiveComponent ψ v h).comapSurjective
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toAddMonoidHom
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.surjective

/-- Transport the actual nontrivial complex-completion restriction to the complex field. -/
def complexCompletionAdditiveCharacter
    (ψ : UnitaryAdditiveCharacter (Adeles K)) {v : InfinitePlace K} (hv : v.IsComplex)
    (h : infiniteAdditiveRestriction ψ v ≠ 1) : UnitaryAdditiveCharacter ℂ :=
  (infiniteAdditiveComponent ψ v h).comapSurjective
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toAddMonoidHom
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.surjective

/-- A nonzero real Fourier scale for the actual infinite restriction. -/
def realCompletionAdditiveScale
    (ψ : UnitaryAdditiveCharacter (Adeles K)) {v : InfinitePlace K} (hv : v.IsReal)
    (h : infiniteAdditiveRestriction ψ v ≠ 1) : ℝˣ :=
  realAdditiveScale (realCompletionAdditiveCharacter ψ hv h)

/-- A nonzero complex trace scale for the actual infinite restriction. -/
def complexCompletionAdditiveScale
    (ψ : UnitaryAdditiveCharacter (Adeles K)) {v : InfinitePlace K} (hv : v.IsComplex)
    (h : infiniteAdditiveRestriction ψ v ≠ 1) : ℂˣ :=
  complexAdditiveScale (complexCompletionAdditiveCharacter ψ hv h)

theorem isRealAdditiveComponent_realCompletionAdditiveScale
    (ψ : UnitaryAdditiveCharacter (Adeles K)) {v : InfinitePlace K} (hv : v.IsReal)
    (h : infiniteAdditiveRestriction ψ v ≠ 1) :
    IsRealAdditiveComponent ψ v hv (realCompletionAdditiveScale ψ hv h) := by
  classical
  intro x
  have hs := realAdditiveScale_spec (realCompletionAdditiveCharacter ψ hv h)
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv x)
  change ψ (infiniteAdditiveInclusion K v
    ((InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv x))) = _ at hs
  simp only [RingEquiv.symm_apply_apply] at hs
  change ψ (Pi.single v x, 0) = _ at hs
  exact hs

theorem isComplexAdditiveComponent_complexCompletionAdditiveScale
    (ψ : UnitaryAdditiveCharacter (Adeles K)) {v : InfinitePlace K} (hv : v.IsComplex)
    (h : infiniteAdditiveRestriction ψ v ≠ 1) :
    IsComplexAdditiveComponent ψ v hv (complexCompletionAdditiveScale ψ hv h) := by
  classical
  intro x
  have hs := complexAdditiveScale_spec (complexCompletionAdditiveCharacter ψ hv h)
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv x)
  change ψ (infiniteAdditiveInclusion K v
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv x))) = _ at hs
  simp only [RingEquiv.symm_apply_apply] at hs
  change ψ (Pi.single v x, 0) = _ at hs
  exact hs

/-- The local-existence conjunct of the global target, conditional only on the
specified actual adelic multiplication-pairing equivalence. -/
theorem localData_of_pairing (χ : HeckeCharacter K)
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (e : Multiplicative (Adeles K) ≃ₜ* PontryaginDual (Multiplicative (Adeles K)))
    (he : ∀ a x : Multiplicative (Adeles K),
      e a x = ψ (Multiplicative.toAdd a * Multiplicative.toAdd x)) :
    (∀ v : FinitePlace K,
      ∃ ψv : @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
          (CompletionPadic.topologicalData v).topology,
        IsFiniteAdditiveComponent ψ v ψv ∧
          Nonempty (LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) ψv)) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsReal),
      (∃ a : ℝˣ, IsRealAdditiveComponent ψ v hv a) ∧
        ∃ d : RealCharacterData, IsRealCharacterPresentation hv (χ.infiniteComponent v) d) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsComplex),
      (∃ a : ℂˣ, IsComplexAdditiveComponent ψ v hv a) ∧
        ∃ d : ComplexCharacterData, IsComplexCharacterPresentation hv (χ.infiniteComponent v) d) := by
  refine ⟨finite_localData_of_pairing ψ e he, ?_, ?_⟩
  · intro v hv
    let h := infiniteAdditiveRestriction_ne_one_of_pairing ψ e he v
    exact ⟨⟨realCompletionAdditiveScale ψ hv h,
        isRealAdditiveComponent_realCompletionAdditiveScale ψ hv h⟩,
      ⟨realCompletionCharacterData hv (χ.infiniteComponent v),
        isRealCharacterPresentation_realCompletionCharacterData hv (χ.infiniteComponent v)⟩⟩
  · intro v hv
    let h := infiniteAdditiveRestriction_ne_one_of_pairing ψ e he v
    exact ⟨⟨complexCompletionAdditiveScale ψ hv h,
        isComplexAdditiveComponent_complexCompletionAdditiveScale ψ hv h⟩,
      ⟨complexCompletionCharacterData hv (χ.infiniteComponent v),
        isComplexCharacterPresentation_complexCompletionCharacterData hv (χ.infiniteComponent v)⟩⟩

end Langlands.Global.HeckeFunctionalEquation
