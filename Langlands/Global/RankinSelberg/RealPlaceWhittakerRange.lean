import Langlands.Global.RankinSelberg.ArchimedeanActualWhittakerIntertwiners
import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryTestsFromGeneration
import Langlands.Global.RankinSelberg.InfiniteWhittakerActualRanges
import Langlands.Global.RankinSelberg.RealAscendingWhittakerEvaluation
import Langlands.Global.RankinSelberg.RealExactStandardEvaluation

/-! # Realizing the full specified Whittaker model at a real place -/

noncomputable section

universe u

open NumberField
open scoped Classical CategoryTheory.MonObj Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic HeckeFunctionalEquation LocalFactor.Archimedean
open Langlands.Archimedean RealPrincipalSeries RealStandardCompactBanach

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

/-- The real Whittaker model lies in the range of any coefficient map with a normalized
identity value on a rank-correct real standard module. -/
theorem realWhittakerModel_le_range_of_normalized {r : ℕ} {d : List RealBlock}
    (hd : realRank d = r + 1) {a : ℝˣ}
    (B₀ : realStandardKFinite (r + 1) d →ₗ[ℂ] (GeneralLinear (r + 1) ℝ → ℂ))
    (hB₀ : IsRealWhittakerIntertwiner r d a B₀) (hNorm : ∃ f, B₀ f 1 = 1) :
    realWhittakerModel r d a ≤ LinearMap.range B₀ := by
  obtain ⟨q, hq, hqInter⟩ := surjectiveIntertwiner_ascendingExpand (r + 1) d hd
  let cs := ascendingCharacters d
  let e := cs.map RealBlock.character
  have hChar : RealStrictCharacterLanglandsQuotient.IsCharacterList e := by
    intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨c, rfl⟩
  have he : realRank e = r + 1 := (realRank_ascendingExpand d).trans hd
  have hLift (B : realStandardKFinite (r + 1) d →ₗ[ℂ] (GeneralLinear (r + 1) ℝ → ℂ))
      (hB : IsRealWhittakerIntertwiner r d a B) := isRealWhittakerIntertwiner_pullback hqInter hB
  obtain ⟨L₀, hL₀⟩ := RealExactStandardEvaluation.exists_standardEvaluation cs a
    (B₀.comp q) (hLift B₀ hB₀)
  obtain ⟨ℓ₀, hBound₀, hCov₀, hCoeff₀⟩ :=
    exists_boundedForm_of_characterEvaluation e hChar a L₀ hL₀.2
  have hℓ₀ : ℓ₀ ≠ 0 := by
    obtain ⟨f, hf⟩ := hNorm
    obtain ⟨g, rfl⟩ := hq f
    intro hz
    have h := (hCoeff₀ g 1).trans (hL₀.1 g 1)
    rw [hz] at h
    exact zero_ne_one (h.trans hf)
  refine iSup_le fun B => iSup_le fun hB => ?_
  obtain ⟨L, hL⟩ := RealExactStandardEvaluation.exists_standardEvaluation cs a (B.comp q) (hLift B hB)
  obtain ⟨ℓ, hBound, hCov, hCoeff⟩ :=
    exists_boundedForm_of_characterEvaluation e hChar a L hL.2
  obtain ⟨z, hz⟩ := hasSmoothWhittakerUniqueness_of_map_character cs he a
    ℓ₀ ℓ hBound₀ hBound hCov₀ hCov hℓ₀
  rintro _ ⟨f, rfl⟩
  obtain ⟨g, rfl⟩ := hq f
  refine ⟨z • q g, funext fun x => ?_⟩
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  calc
    z * B₀ (q g) x = z * functionalCoefficient e ℓ₀ g x :=
      congrArg (z * ·) ((hCoeff₀ g x).trans (hL₀.1 g x)).symm
    _ = functionalCoefficient e ℓ g x := by rw [hz]; rfl
    _ = B (q g) x := (hCoeff g x).trans (hL.1 g x)

/-- Every function in the specified real Whittaker model of an actual cuspidal
realization is its adelic Whittaker restriction with finite coordinate one. -/
def RealPlaceWhittakerRangeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r)
    (v : {w : InfinitePlace F // w.IsReal}) (d : List RealBlock),
    T.realization.HasRealPlaceParameter v d →
  ∀ (a : ℝˣ), IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ W : GeneralLinear (r + 1) ℝ → ℂ, W ∈ realWhittakerModel r d a →
    ∃ x : T.Space, ∀ g, W g = cuspWhittaker F T ψ.complex x (realPlacePoint F (r + 1) v g)

theorem realPlaceWhittakerRange : RealPlaceWhittakerRangeStatement.{u} := by
  intro F _ _ _ ψ hψ r T v d hd a ha W hW
  obtain ⟨A, B, _, hB, hNorm, hValue⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ r T).1 v d hd a ha
  obtain ⟨f, rfl⟩ := realWhittakerModel_le_range_of_normalized hd.1 B hB hNorm hW
  exact ⟨A f, hValue f⟩

/-- Both characters of an opposite pair of Whittaker models have actual realizations. -/
theorem realWhittakerRestrictionOnto : RealPlaceWhittakerRestrictionOntoStatement.{u} := by
  intro F _ _ _ ψ hψ r T v a ha d hd W
  constructor
  · intro hW
    obtain ⟨x, hx⟩ := realPlaceWhittakerRange F ψ hψ r T v d hd a ha W hW
    exact ⟨x, 1, funext fun g => by rw [InfiniteWhittakerSlice.finitePoint_one, mul_one, hx g]⟩
  · intro hW
    have ha' : IsRealAdditiveComponent (inverseCharacter ψ) v.1 v.2 (-a) := by
      intro x
      apply Subtype.ext
      simpa only [← complex_inverseCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply]
        using realComponent_complex_inv ψ v a ha x
    obtain ⟨x, hx⟩ := realPlaceWhittakerRange F (inverseCharacter ψ) (inverseCharacter_rational ψ hψ)
      r T v d hd (-a) ha' W hW
    refine ⟨x, 1, funext fun g => ?_⟩
    rw [InfiniteWhittakerSlice.finitePoint_one, mul_one]
    simpa only [complex_inverseCharacter] using hx g

end Langlands.Global.RankinSelbergGlobal
