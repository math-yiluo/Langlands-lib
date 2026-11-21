import Langlands.Global.RankinSelberg.ComplexSmoothWhittakerMultiplicityOne
import Langlands.Global.RankinSelberg.ComplexSmoothWhittakerEquivariance
import Langlands.Global.RankinSelberg.ComplexJacquetNonzero
import Langlands.Global.RankinSelberg.ComplexJacquetIntertwiner

/-! # The exact complex Whittaker model is the canonical Jacquet range -/

noncomputable section

open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetMultiplicityOne

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner complexJacquetNonzero)
open ComplexSmoothWhittakerEquivariance (complexSmoothWhittakerEquivariance)
open ComplexSmoothWhittakerMultiplicityOne (complexSmoothWhittakerMultiplicityOne)
open ComplexWhittakerSmoothExtension (finiteToSmooth)
open ComplexWhittakerTranslateExtension (smoothTranslate)

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℂ
local notation "Std" => fun r ds => Automorphic.complexStandardKFinite (r + 1) ds

/-- Every list of the specified length is an exact parameter list, with its original
character data. -/
theorem exists_characterList {n : ℕ} (ds : List ComplexCharacterData) (hds : ds.length = n) :
    ∃ (l : Fin n → ℤ) (p : Fin n → ℂ), characterList l p = ds := by
  subst n
  refine ⟨fun i => (ds.get i).weight, fun i => (ds.get i).exponent, ?_⟩
  calc
    characterList (fun i => (ds.get i).weight) (fun i => (ds.get i).exponent) = List.ofFn ds.get :=
      congrArg List.ofFn (funext fun i => Langlands.Archimedean.characterOfParams_eta (ds.get i))
    _ = ds := List.ofFn_get ds

/-- Exact Whittaker intertwiners are proportional to a fixed nonzero exact intertwiner. -/
theorem exactIntertwiner_proportional (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B B₀ : Std r ds →ₗ[ℂ] (G r → ℂ)) (hB : IsComplexWhittakerIntertwiner r ds a B)
    (hB₀ : IsComplexWhittakerIntertwiner r ds a B₀) (hNonzero : B₀ ≠ 0) :
    ∃ c : ℂ, B = c • B₀ := by
  obtain ⟨L, J, C, hC, hVal, hBound, hCov⟩ := complexSmoothWhittakerEquivariance r ds a B hB
  obtain ⟨L₀, J₀, C₀, hC₀, hVal₀, hBound₀, hCov₀⟩ := complexSmoothWhittakerEquivariance r ds a B₀ hB₀
  have hNonzero₀ : L₀ ≠ 0 := by
    intro h
    apply hNonzero
    apply LinearMap.ext
    intro f
    funext g
    rw [← hVal₀ f g, h]
    rfl
  obtain ⟨c, hc⟩ := complexSmoothWhittakerMultiplicityOne r ds a L L₀
    ⟨J, C, hC, hBound, hCov⟩ ⟨J₀, C₀, hC₀, hBound₀, hCov₀⟩ hNonzero₀
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro f
  funext g
  change B f g = c * B₀ f g
  rw [← hVal f g, ← hVal₀ f g, hc]
  rfl

/-- The full exact Whittaker model is the range of each nonzero exact intertwiner. -/
theorem model_eq_range_of_nonzero (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B₀ : Std r ds →ₗ[ℂ] (G r → ℂ)) (hB₀ : IsComplexWhittakerIntertwiner r ds a B₀)
    (hNonzero : B₀ ≠ 0) : complexWhittakerModel r ds a = LinearMap.range B₀ := by
  unfold complexWhittakerModel
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨c, hc⟩ := exactIntertwiner_proportional r ds a B B₀ hB hB₀ hNonzero
    rintro W ⟨f, rfl⟩
    exact ⟨c • f, by rw [hc, map_smul]; rfl⟩
  · exact le_iSup_of_le B₀ (le_iSup (fun _ : IsComplexWhittakerIntertwiner r ds a B₀ => LinearMap.range B₀) hB₀)

private theorem continuedJacquet_ne_zero (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ) : continuedJacquet μ a l p ≠ 0 := by
  obtain ⟨f, hf⟩ := complexJacquetNonzero r μ a l p
  intro h
  exact hf (by rw [h]; rfl)

/-- At every parameter the canonical Jacquet intertwiner spans the exact intertwiners
and has range equal to the exact Whittaker model. -/
def ComplexJacquetMultiplicityOneStatement : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ),
    (∀ B : Std r (characterList l p) →ₗ[ℂ] (G r → ℂ),
      IsComplexWhittakerIntertwiner r (characterList l p) (-a) B →
        ∃ c : ℂ, B = c • continuedJacquet μ a l p) ∧
    complexWhittakerModel r (characterList l p) (-a) = LinearMap.range (continuedJacquet μ a l p)

theorem complexJacquetMultiplicityOne : ComplexJacquetMultiplicityOneStatement := by
  intro r μ a l p
  let B₀ := continuedJacquet μ a l p
  have hB₀ := complexJacquetIntertwiner r μ a l p
  have hNonzero := continuedJacquet_ne_zero r μ a l p
  exact ⟨fun B hB => exactIntertwiner_proportional r (characterList l p) (-a) B B₀ hB hB₀ hNonzero,
    model_eq_range_of_nonzero r (characterList l p) (-a) B₀ hB₀ hNonzero⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetMultiplicityOne
