import Langlands.Global.Factors.CuspidalPairPoleRealRestrictionReduction
import Langlands.Global.RankinSelberg.RealAscendingWhittakerEvaluation
import Langlands.Global.RankinSelberg.RealExactStandardEvaluation

/-! # Surjectivity of real cuspidal Whittaker restriction -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal RealPrincipalSeries RealStandardCompactBanach
open RealStrictCharacterLanglandsQuotient (IsCharacterList)

private local instance (n : ℕ) (d : List RealBlock) : NormedAddCommGroup (Carrier n d) :=
  (closureSubmodule (n := n) d).normedAddCommGroup

private local instance (n : ℕ) (d : List RealBlock) : NormedSpace ℂ (Carrier n d) :=
  (closureSubmodule (n := n) d).normedSpace

local notation:max "RG" r:max => Langlands.GeneralLinear (r + 1) ℝ
local notation:max "Std" r:max d:max => Automorphic.realStandardKFinite (r + 1) d

private theorem exists_boundedForm_ascending {r : ℕ} (d : List RealBlock) (a : ℝˣ)
    (B : Std r (ascendingExpand d) →ₗ[ℂ] (RG r → ℂ))
    (hB : IsRealWhittakerIntertwiner r (ascendingExpand d) a B) :
    ∃ ℓ : principalSeries ℝ (r + 1) (realPositionCharacter (ascendingExpand d)) →ₗ[ℂ] ℂ,
      HasCompactDerivativeBound r (ascendingExpand d) ℓ ∧
      HasWhittakerCovariance (ascendingExpand d) a ℓ ∧
      ∀ f g, functionalCoefficient (ascendingExpand d) ℓ f g = B f g := by
  have hChars : IsCharacterList (ascendingExpand d) := by
    intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨c, rfl⟩
  obtain ⟨L, hL⟩ := RealExactStandardEvaluation.exists_standardEvaluation
    (ascendingCharacters d) a B hB
  obtain ⟨ℓ, hBound, hCov, hCoe⟩ :=
    exists_boundedForm_of_characterEvaluation (ascendingExpand d) hChars a L hL.2
  exact ⟨ℓ, hBound, hCov, fun f g => (hCoe f g).trans (hL.1 f g)⟩

private theorem realWhittakerModel_le_normalizedRange {r : ℕ} (d : List RealBlock)
    (hd : realRank d = r + 1) (a : ℝˣ) (B₀ : Std r d →ₗ[ℂ] (RG r → ℂ))
    (hB₀ : IsRealWhittakerIntertwiner r d a B₀) (hNorm : ∃ f, B₀ f 1 = 1) :
    realWhittakerModel r d a ≤ LinearMap.range B₀ := by
  obtain ⟨T, hSurj, hT⟩ := surjectiveIntertwiner_ascendingExpand (r + 1) d hd
  obtain ⟨ℓ₀, hBound₀, hCov₀, hCoe₀⟩ := exists_boundedForm_ascending d a (B₀.comp T)
    (isRealWhittakerIntertwiner_pullback hT hB₀)
  have hne : ℓ₀ ≠ 0 := by
    obtain ⟨f₀, hf₀⟩ := hNorm
    obtain ⟨v₀, hv₀⟩ := hSurj f₀
    intro hz
    have h := hCoe₀ v₀ 1
    rw [hz, LinearMap.comp_apply, hv₀, hf₀] at h
    exact zero_ne_one h
  refine iSup₂_le fun B hB => ?_
  obtain ⟨ℓ, hBound, hCov, hCoe⟩ := exists_boundedForm_ascending d a (B.comp T)
    (isRealWhittakerIntertwiner_pullback hT hB)
  obtain ⟨c, hc⟩ := hasSmoothWhittakerUniqueness_of_map_character (ascendingCharacters d)
    ((realRank_ascendingExpand d).trans hd) a ℓ₀ ℓ hBound₀ hBound hCov₀ hCov hne
  rintro _ ⟨f, rfl⟩
  obtain ⟨v, rfl⟩ := hSurj f
  refine ⟨c • T v, funext fun g => ?_⟩
  rw [map_smul]
  calc
    (c • B₀ (T v)) g = c * functionalCoefficient (ascendingExpand d) ℓ₀ v g :=
      congrArg (c * ·) (hCoe₀ v g).symm
    _ = functionalCoefficient (ascendingExpand d) ℓ v g := by rw [hc]; rfl
    _ = B (T v) g := hCoe v g

/-- For both compatible characters, every function in the specified real
Whittaker model is a restriction from the given cuspidal realization. -/
theorem realPlaceWhittakerRestrictionSurjectivity :
    RealPlaceWhittakerRestrictionSurjectivityStatement.{u} :=
  realPlaceWhittakerRestrictionFromNormalizedRange
    (fun _ d hd a B _ hB hNorm => realWhittakerModel_le_normalizedRange d hd a B hB hNorm)

end Langlands.Global.CuspidalPairPoles
