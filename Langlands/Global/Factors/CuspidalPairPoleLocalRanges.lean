import Langlands.Global.Factors.CuspidalPairPoleUnequalLocalTests
import Langlands.Global.RankinSelberg.ArchimedeanPlaceWhittakerModels
import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerSliceReduction
import Langlands.Global.RankinSelberg.InfiniteWhittakerActualRanges

/-! # Specified local Whittaker ranges from actual restriction surjectivity -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField Set
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic CompletionPadic RankinSelbergGlobal FiniteWhittakerDual InfiniteWhittakerSlice
open FiniteWhittakerTensor FiniteWhittakerModel
open CuspidalPairFunctionalEquation HeckeFunctionalEquation
open LocalFactor.Archimedean
open Whittaker (IsGeneric)

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- Each model function at a real place is realized by an actual restriction, for both
signs of the standard adelic character and for the supplied standard parameter. -/
def RealPlaceWhittakerRestrictionSurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r), IsTrivialOnSplitCentre T →
  ∀ (v : RP F) (a : ℝˣ), IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ d : List RealBlock, T.realization.HasRealPlaceParameter v d →
  ∀ W : GeneralLinear (r + 1) ℝ → ℂ,
    (W ∈ realWhittakerModel r d a → IsRealPlaceWhittaker F T ψ.complex v W) ∧
    (W ∈ realWhittakerModel r d (-a) → IsRealPlaceWhittaker F T ψ.complex⁻¹ v W)

/-- Each model function at a complex place is realized by an actual restriction, for both
signs of the standard adelic character and for the supplied standard parameter. -/
def ComplexPlaceWhittakerRestrictionSurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r), IsTrivialOnSplitCentre T →
  ∀ (w : CP F) (a : ℂˣ), IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ d : List ComplexCharacterData, T.realization.HasComplexPlaceParameter w d →
  ∀ W : GeneralLinear (r + 1) ℂ → ℂ,
    (W ∈ complexWhittakerModel r d a → IsComplexPlaceWhittaker F T ψ.complex w W) ∧
    (W ∈ complexWhittakerModel r d (-a) → IsComplexPlaceWhittaker F T ψ.complex⁻¹ w W)

/-- Compare actual tensor slices to the full specified coefficient models for both
characters of one cuspidal realization over a fixed field. -/
def SpecifiedWhittakerSliceComparisonAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r), IsTrivialOnSplitCentre T →
  ∀ (P : CuspidalSpectralPresentation.{u,uQ} T) (hP : HasIrreducibleAdmissibleComponents P)
    (aR : (RP F) → ℝˣ), (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : (CP F) → ℂˣ), (∀ w, IsComplexAdditiveComponent ψ w.1 w.2 (aC w)) →
  ∀ (dR : (RP F) → List RealBlock), (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
  ∀ (dC : (CP F) → List ComplexCharacterData), (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    ∃ (M : ModelData P hP ψ.complex) (N : ModelData P hP (inverseCharacter ψ).complex),
      HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC ∧
      HasSpecifiedWhittakerSliceRanges (P := P) (ψ := inverseCharacter ψ)
        N (fun v => -aR v) (fun w => -aC w) dR dC

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}

local instance poleLocalRangesAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleLocalRangesSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance poleLocalRangesRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleLocalRangesContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleLocalRangesFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleLocalRangesAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleLocalRangesStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance poleLocalRangesLocalGroup (v : FinitePlace F) (A : LocalRealization F (r + 1) v) :
    AddCommGroup A.Space := Submodule.addCommGroup _

private theorem exists_normalizedFactorFunctional (P : CuspidalSpectralPresentation.{u,uQ} T)
    (hP : HasIrreducibleAdmissibleComponents P) (hT : IsTrivialOnSplitCentre T) (v : FinitePlace F)
    (ψv : Correspondence.NontrivialAdditiveCharacter (padicField v)) :
    ∃ (ℓ : FactorFunctionals P v ψv) (a : P.localFactor v), ℓ.val a = 1 := by
  let _ : TopologicalSpace (padicField v).Carrier := (padicField v).canonicalTopologicalData.topology
  have h := cuspidalUnitaryLocalGenericity F r T (cuspidalSplitCentreUnitaryCentralCharacter F r T hT)
    P v (hP v).1 (hP v).2 ψv
  obtain ⟨l, hl⟩ := h.2.2
  let ℓ := factorFunctional P v ψv l
  obtain ⟨a, ha⟩ := normalizedVector ℓ.val (factorFunctional_ne_zero P v ψv l hl)
  exact ⟨ℓ, a, ha⟩

/-- The finite genericity of a cuspidal presentation supplies the normalized finite
reference tuple that identifies the ranges of its compared infinite slices. -/
theorem hasActualPlaceWhittakerRanges_of_cuspidal
    {P : CuspidalSpectralPresentation.{u,uQ} T} {hP : HasIrreducibleAdmissibleComponents P}
    (hT : IsTrivialOnSplitCentre T) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (M : ModelData P hP ψ.complex) :
    HasActualPlaceWhittakerRanges (P := P) (ψ := ψ) M := by
  obtain ⟨A, hA⟩ := exists_finiteAdditiveSupport ψ hψ
  let S := P.exceptional ∪ A
  let ψv (v : S) := canonicalFiniteAdditiveComponent ψ hψ v.1
  choose ℓ a ha using fun v : S => exists_normalizedFactorFunctional P hP hT v.1 (ψv v)
  exact hasActualPlaceWhittakerRanges (S := S) M hψ Finset.subset_union_left
    (finiteAdditiveSupport_mono hA Finset.subset_union_right) ψv
    (fun v => isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hψ v.1) ℓ a ha

/-- The normalized slice comparison and the converse local restrictions produce exactly
the full model ranges required by the ordinary global test constructions. -/
theorem specifiedWhittakerSliceComparisonAt_of_local
    (hSlice : InfiniteWhittakerSliceModelStatement.{u,uQ})
    (hReal : RealPlaceWhittakerRestrictionSurjectivityStatement.{u})
    (hComplex : ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u}) :
    SpecifiedWhittakerSliceComparisonAt.{u,uQ} F := by
  intro ψ hψ r T hT P hP aR haR aC haC dR hdR dC hdC
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  let ψ' := inverseCharacter ψ
  have hψ' (x : F) : ψ' (algebraMap F (Adeles F) x) = 1 := by
    change inverseCharacter ψ _ = 1
    rw [inverseCharacter_apply, hψ, inv_one]
  have hχ' := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ' hψ'
  let M := Classical.choice (hSlice F r T P hP ψ.complex hχ dR hdR dC hdC)
  let N := Classical.choice (hSlice F r T P hP ψ'.complex hχ' dR hdR dC hdC)
  have hM := hasActualPlaceWhittakerRanges_of_cuspidal hT ψ hψ M
  have hN := hasActualPlaceWhittakerRanges_of_cuspidal hT ψ' hψ' N
  refine ⟨M, N, ⟨fun v => le_antisymm ?_ ?_, fun w => le_antisymm ?_ ?_⟩,
    ⟨fun v => le_antisymm ?_ ?_, fun w => le_antisymm ?_ ?_⟩⟩
  · intro W hW
    exact RealUniformWhittaker.model_le_model (dR v) (aR v)
      ((archimedeanPlaceWhittakerModels.1 F ψ hψ r T v (aR v) (haR v) (dR v) (hdR v) W).1
        ((hM.1 v W).mp hW))
  · intro W hW
    exact (hM.1 v W).mpr ((hReal F ψ hψ r T hT v (aR v) (haR v) (dR v) (hdR v) W).1 hW)
  · intro W hW
    exact (archimedeanPlaceWhittakerModels.2 F ψ hψ r T w (aC w) (haC w) (dC w) (hdC w) W).1
      ((hM.2 w W).mp hW)
  · intro W hW
    exact (hM.2 w W).mpr ((hComplex F ψ hψ r T hT w (aC w) (haC w) (dC w) (hdC w) W).1 hW)
  · intro W hW
    apply RealUniformWhittaker.model_le_model (dR v) (-aR v)
      ((archimedeanPlaceWhittakerModels.1 F ψ hψ r T v (aR v) (haR v) (dR v) (hdR v) W).2 ?_)
    simpa only [ψ', complex_inverseCharacter] using (hN.1 v W).mp hW
  · intro W hW
    apply (hN.1 v W).mpr
    simpa only [ψ', complex_inverseCharacter] using (hReal F ψ hψ r T hT v (aR v) (haR v) (dR v) (hdR v) W).2 hW
  · intro W hW
    apply (archimedeanPlaceWhittakerModels.2 F ψ hψ r T w (aC w) (haC w) (dC w) (hdC w) W).2
    simpa only [ψ', complex_inverseCharacter] using (hN.2 w W).mp hW
  · intro W hW
    apply (hN.2 w W).mpr
    simpa only [ψ', complex_inverseCharacter] using (hComplex F ψ hψ r T hT w (aC w) (haC w) (dC w) (hdC w) W).2 hW

end Langlands.Global.CuspidalPairPoles
