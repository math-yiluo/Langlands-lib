import Langlands.Global.Factors.CuspidalPairPoleLocalRanges
import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RankOneWhittakerSlice

/-! # The specified Whittaker slice ranges in rank one -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField
open scoped Classical CategoryTheory.MonObj

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal InfiniteWhittakerSlice
open CuspidalPairFunctionalEquation HeckeFunctionalEquation LocalFactor.Archimedean

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

private theorem eq_of_normalized_character_line {G : Type*} [One G]
    {U V : Submodule ℂ (G → ℂ)} {f : G → ℂ} (hf : f 1 = 1) (hle : U ≤ V)
    (hV : ∀ W ∈ V, ∃ c : ℂ, ∀ g, W g = c * f g)
    (hU : ∃ W ∈ U, W 1 = 1) : U = V := by
  obtain ⟨W₀, hW₀, hW₀₁⟩ := hU
  obtain ⟨c, hc⟩ := hV W₀ (hle hW₀)
  have hc₁ : c = 1 := by simpa only [hW₀₁, hf, mul_one] using (hc 1).symm
  have hW₀f : W₀ = f := funext fun g => by rw [hc g, hc₁, one_mul]
  refine le_antisymm hle fun W hW => ?_
  obtain ⟨a, ha⟩ := hV W hW
  have hWf : W = a • f := funext ha
  rw [hWf, ← hW₀f]
  exact U.smul_mem a hW₀

private theorem realRange_rankOne {U : Submodule ℂ (Langlands.GeneralLinear 1 ℝ → ℂ)}
    {d : List RealBlock} {a : ℝˣ} (hd : realRank d = 1)
    (hle : U ≤ realWhittakerModel 0 d a) (hU : ∃ W ∈ U, W 1 = 1) :
    U = realWhittakerModel 0 d a := by
  obtain ⟨c, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hd
  exact eq_of_normalized_character_line
    (f := fun g => (c.character (GeneralLinear.determinant g) : ℂ)) (by simp)
    hle (fun _ hW => RealRankZero.exists_eq_of_mem_realWhittakerModel hW) hU

private theorem complexRange_rankOne {U : Submodule ℂ (Langlands.GeneralLinear 1 ℂ → ℂ)}
    {d : List ComplexCharacterData} {a : ℂˣ} (hd : d.length = 1)
    (hle : U ≤ complexWhittakerModel 0 d a) (hU : ∃ W ∈ U, W 1 = 1) :
    U = complexWhittakerModel 0 d a := by
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd
  exact eq_of_normalized_character_line
    (f := fun g => (c.character (GeneralLinear.determinant g) : ℂ)) (by simp)
    hle (fun _ hW => ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW) hU

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The specified range comparison for an actual cuspidal GL₁ presentation. -/
def RankOneSpecifiedWhittakerSliceComparisonAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (T : CuspidalOperatorRealization F 0), IsTrivialOnSplitCentre T →
  ∀ (P : CuspidalSpectralPresentation.{u,uQ} T) (hP : HasIrreducibleAdmissibleComponents P)
    (aR : (RP F) → ℝˣ), (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : (CP F) → ℂˣ), (∀ w, IsComplexAdditiveComponent ψ w.1 w.2 (aC w)) →
  ∀ (dR : (RP F) → List RealBlock), (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
  ∀ (dC : (CP F) → List ComplexCharacterData), (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    ∃ (M : ModelData P hP ψ.complex) (N : ModelData P hP (inverseCharacter ψ).complex),
      HasSpecifiedWhittakerSliceRanges (P := P) (ψ := ψ) M aR aC dR dC ∧
      HasSpecifiedWhittakerSliceRanges (P := P) (ψ := inverseCharacter ψ)
        N (fun v => -aR v) (fun w => -aC w) dR dC

set_option maxHeartbeats 4000000 in
theorem rankOneSpecifiedWhittakerSliceComparisonAt : RankOneSpecifiedWhittakerSliceComparisonAt.{u,uQ} F := by
  intro ψ hψ T hT P hP aR haR aC haC dR hdR dC hdC
  let ψ' := inverseCharacter ψ
  have hψ' (x : F) : ψ' (algebraMap F (Adeles F) x) = 1 := by
    change inverseCharacter ψ _ = 1
    rw [inverseCharacter_apply, hψ, inv_one]
  obtain ⟨M⟩ := rankOneWhittakerSlice F T P hP ψ.complex
  obtain ⟨N⟩ := rankOneWhittakerSlice F T P hP ψ'.complex
  have hM := hasActualPlaceWhittakerRanges_of_cuspidal hT ψ hψ M
  have hN := hasActualPlaceWhittakerRanges_of_cuspidal hT ψ' hψ' N
  refine ⟨M, N, ⟨fun v => realRange_rankOne (hdR v).1 ?_ ?_, fun w =>
    complexRange_rankOne (hdC w).1 ?_ ?_⟩, ⟨fun v => realRange_rankOne (hdR v).1 ?_ ?_, fun w =>
    complexRange_rankOne (hdC w).1 ?_ ?_⟩⟩
  · intro W hW
    exact RealUniformWhittaker.model_le_model (dR v) (aR v)
      ((archimedeanPlaceWhittakerModels.1 F ψ hψ 0 T v (aR v) (haR v) (dR v) (hdR v) W).1
        ((hM.1 v W).mp hW))
  · obtain ⟨b, hb⟩ := M.normalized (.inl v)
    exact ⟨M.model (.inl v) b, ⟨b, rfl⟩, hb⟩
  · intro W hW
    exact (archimedeanPlaceWhittakerModels.2 F ψ hψ 0 T w (aC w) (haC w) (dC w) (hdC w) W).1
      ((hM.2 w W).mp hW)
  · obtain ⟨b, hb⟩ := M.normalized (.inr w)
    exact ⟨M.model (.inr w) b, ⟨b, rfl⟩, hb⟩
  · intro W hW
    apply RealUniformWhittaker.model_le_model (dR v) (-aR v)
      ((archimedeanPlaceWhittakerModels.1 F ψ hψ 0 T v (aR v) (haR v) (dR v) (hdR v) W).2 ?_)
    simpa only [ψ', complex_inverseCharacter] using (hN.1 v W).mp hW
  · obtain ⟨b, hb⟩ := N.normalized (.inl v)
    exact ⟨N.model (.inl v) b, ⟨b, rfl⟩, hb⟩
  · intro W hW
    apply (archimedeanPlaceWhittakerModels.2 F ψ hψ 0 T w (aC w) (haC w) (dC w) (hdC w) W).2
    simpa only [ψ', complex_inverseCharacter] using (hN.2 w W).mp hW
  · obtain ⟨b, hb⟩ := N.normalized (.inr w)
    exact ⟨N.model (.inr w) b, ⟨b, rfl⟩, hb⟩

end Langlands.Global.CuspidalPairPoles
