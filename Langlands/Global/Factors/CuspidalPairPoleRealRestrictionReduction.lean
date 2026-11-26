import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof
import Langlands.Global.Factors.CuspidalPairPoleLocalRanges
import Langlands.Global.RankinSelberg.ArchimedeanActualWhittakerIntertwiners
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerIdentityEvaluation
import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests

/-! # Real cuspidal restriction from local Whittaker range comparison -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

universe u

namespace Langlands.Global.CuspidalPairPoles

open Automorphic HeckeFunctionalEquation LocalFactor.Archimedean RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

local notation:max "RP" F:max => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation:max "Std" r:max d:max => realStandardKFinite (r + 1) d
local notation:max "RG" r:max => GeneralLinear (r + 1) ℝ

/-- In positive semisimple rank, a real coefficient map whose identity value is
normalized on a vector of the specified irreducible standard module spans the model. -/
def RealWhittakerNormalizedRangeStatement : Prop :=
  ∀ (s : ℕ) (d : List RealBlock), realRank d = s + 1 + 1 →
  ∀ (a : ℝˣ) (B : Std (s + 1) d →ₗ[ℂ] (RG (s + 1) → ℂ)),
    Archimedean.IsIrreducibleGKModule (Archimedean.realStandardRep (s + 1 + 1) d)
      (Archimedean.realStandardLie (s + 1 + 1) d) →
    IsRealWhittakerIntertwiner (s + 1) d a B →
    (∃ f, B f 1 = 1) → realWhittakerModel (s + 1) d a ≤ LinearMap.range B

private theorem rankOne_model_le_range {d : List RealBlock} (hd : realRank d = 1)
    {a : ℝˣ} (B : Std 0 d →ₗ[ℂ] (RG 0 → ℂ)) (hB : IsRealWhittakerIntertwiner 0 d a B)
    {f : Std 0 d} (hf : B f 1 = 1) : realWhittakerModel 0 d a ≤ LinearMap.range B := by
  obtain ⟨c, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hd
  have hmem : B f ∈ realWhittakerModel 0 [.character c] a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  obtain ⟨b, hb⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel hmem
  have hb₁ : b = 1 := by simpa [hf] using (hb 1).symm
  rw [hb₁] at hb
  intro W hW
  obtain ⟨z, hz⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel hW
  refine ⟨z • f, funext fun g => ?_⟩
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hb, one_mul, hz]

variable {F : Type u} [Field F] [NumberField F]

private theorem isRealAdditiveComponent_inverse
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {v : RP F} {a : ℝˣ}
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a) :
    IsRealAdditiveComponent (inverseCharacter ψ) v.1 v.2 (-a) := by
  intro x
  apply Subtype.ext
  simpa only [← complex_inverseCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply]
    using realComponent_complex_inv ψ v a ha x

variable [CompactSpace (AdeleQuotient F)]

private theorem restrict_of_model_le_range
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r : ℕ} (T : CuspidalOperatorRealization F r) (v : RP F) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a) (d : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d)
    (hRange : ∀ B : Std r d →ₗ[ℂ] (RG r → ℂ), IsRealWhittakerIntertwiner r d a B →
      (∃ f, B f 1 = 1) → realWhittakerModel r d a ≤ LinearMap.range B)
    {W : RG r → ℂ} (hW : W ∈ realWhittakerModel r d a) : IsRealPlaceWhittaker F T ψ.complex v W := by
  obtain ⟨A, B, _, hB, hNorm, hValue⟩ := (archimedeanActualWhittakerIntertwiners F ψ hψ r T).1 v d hd a ha
  obtain ⟨f, rfl⟩ := hRange B hB hNorm hW
  have hFinite : finitePoint F (r + 1) 1 = 1 := by
    exact ArchimedeanWhittakerEvaluation.adelicPoint_one
  exact ⟨A f, 1, funext fun g => by simpa only [hFinite, mul_one] using hValue f g⟩

private theorem restrict_both_of_model_le_range
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r : ℕ} (T : CuspidalOperatorRealization F r) (v : RP F) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a) (d : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d)
    (hRange : ∀ (b : ℝˣ) (B : Std r d →ₗ[ℂ] (RG r → ℂ)), IsRealWhittakerIntertwiner r d b B →
      (∃ f, B f 1 = 1) → realWhittakerModel r d b ≤ LinearMap.range B)
    (W : RG r → ℂ) :
    (W ∈ realWhittakerModel r d a → IsRealPlaceWhittaker F T ψ.complex v W) ∧
    (W ∈ realWhittakerModel r d (-a) → IsRealPlaceWhittaker F T ψ.complex⁻¹ v W) := by
  refine ⟨restrict_of_model_le_range ψ hψ T v a ha d hd (hRange a), fun hW => ?_⟩
  rw [← complex_inverseCharacter]
  exact restrict_of_model_le_range (inverseCharacter ψ) (inverseCharacter_rational ψ hψ)
    T v (-a) (isRealAdditiveComponent_inverse ha) d hd (hRange (-a)) hW

/-- Both real restriction implications hold unconditionally for `GL₁`. -/
theorem realPlaceWhittakerRestriction_rankOne
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (T : CuspidalOperatorRealization F 0) (v : RP F) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a) (d : List RealBlock)
    (hd : T.realization.HasRealPlaceParameter v d) (W : RG 0 → ℂ) :
    (W ∈ realWhittakerModel 0 d a → IsRealPlaceWhittaker F T ψ.complex v W) ∧
    (W ∈ realWhittakerModel 0 d (-a) → IsRealPlaceWhittaker F T ψ.complex⁻¹ v W) :=
  restrict_both_of_model_le_range ψ hψ T v a ha d hd
    (fun _ B hB ⟨_, hf⟩ => rankOne_model_le_range hd.1 B hB hf) W

/-- The real restriction comparison in every rank follows from the normalized
local range inclusion in positive semisimple rank. -/
def RealPlaceWhittakerRestrictionFromNormalizedRangeStatement : Prop :=
  RealWhittakerNormalizedRangeStatement → RealPlaceWhittakerRestrictionSurjectivityStatement.{u}

theorem realPlaceWhittakerRestrictionFromNormalizedRange :
    RealPlaceWhittakerRestrictionFromNormalizedRangeStatement.{u} := by
  intro hLocal F _ _ _ ψ hψ r T _ v a ha d hd W
  apply restrict_both_of_model_le_range ψ hψ T v a ha d hd _ W
  intro b B hB hNorm
  cases r with
  | zero =>
    obtain ⟨f, hf⟩ := hNorm
    exact rankOne_model_le_range hd.1 B hB hf
  | succ s => exact hLocal s d hd.1 b B (T.isIrreducibleRealStandard v d hd) hB hNorm

end Langlands.Global.CuspidalPairPoles
