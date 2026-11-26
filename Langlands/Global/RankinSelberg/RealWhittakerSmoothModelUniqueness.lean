import Langlands.Global.RankinSelberg.RealAscendingWhittakerEvaluation

/-! # Uniqueness of the uniform real Whittaker maps from smooth extension -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open RealPrincipalSeries RealStrictCharacterLanglandsQuotient

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (d : List RealBlock) : NormedAddCommGroup (Carrier n d) :=
  (closureSubmodule (n := n) d).normedAddCommGroup

private local instance (n : ℕ) (d : List RealBlock) : NormedSpace ℂ (Carrier n d) :=
  (closureSubmodule (n := n) d).normedSpace

private theorem ascending_isCharacterList (d : List RealBlock) : IsCharacterList (ascendingExpand d) := by
  intro b hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨c, rfl⟩

variable {r : ℕ}

local notation "RG" => Langlands.GeneralLinear (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation:max "V" d:max => Automorphic.realStandardKFinite (r + 1) d
local notation:max "R" d:max => representation (n := r + 1) d
local notation:max "D" d:max => DerivativeSmoothVectors I (R d)
local notation:max "act" d:max => DerivativeSmoothVectors.representation I (R d)

/-- Smooth extension and principal-series uniqueness compare two uniform real
coefficient maps on the same irreducible standard module. -/
private theorem exists_smul_of_normalized_realUniformIntertwiner
    (hCW : RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0})
    (d : List RealBlock) (hd : realRank d = r + 1) (a : ℝˣ)
    (hIrr : IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d))
    (B₀ B : V d →ₗ[ℂ] (RG → ℂ))
    (hB₀ : IsRealUniformWhittakerIntertwiner r d a B₀)
    (hB : IsRealUniformWhittakerIntertwiner r d a B)
    (hNorm : ∃ f, B₀ f 1 = 1) : ∃ c : ℂ, B = c • B₀ := by
  obtain ⟨L₀, hL₀, _⟩ := realSmoothWhittakerEvaluation hCW r d a B₀ hIrr hB₀
  obtain ⟨L, hL, _⟩ := realSmoothWhittakerEvaluation hCW r d a B hIrr hB
  let e := ascendingExpand d
  obtain ⟨T, hT, hpre⟩ := smoothStandardQuotient_ascendingExpand r d hd
  have hCov (M : V d →ₗ[ℂ] (RG → ℂ)) (J : (D d) →L[ℂ] ℂ)
      (hJ : IsWhittakerStandardEvaluation d a M J) (u : U) (v : D e) :
      (J.comp T) (act e u.val v) = realWhittakerCharacter a u.val * (J.comp T) v := by
    exact (congrArg J (hT u.val v)).trans (hJ.2 u (T v))
  obtain ⟨ℓ₀, hBound₀, hCov₀, hCoe₀⟩ := exists_boundedForm_of_characterEvaluation (r := r)
    e (ascending_isCharacterList d) a (L₀.comp T) (hCov B₀ L₀ hL₀)
  obtain ⟨ℓ, hBound, hCov₁, hCoe⟩ := exists_boundedForm_of_characterEvaluation (r := r)
    e (ascending_isCharacterList d) a (L.comp T) (hCov B L hL)
  have hMatch {f : V d} {g' : V e} (hg' : T (compactFiniteEquiv e g').val = (compactFiniteEquiv d f).val)
      (g : RG) : functionalCoefficient e ℓ₀ g' g = B₀ f g ∧ functionalCoefficient e ℓ g' g = B f g := by
    constructor
    · rw [hCoe₀, ContinuousLinearMap.comp_apply, hT, hg']
      exact hL₀.1 f g
    · rw [hCoe, ContinuousLinearMap.comp_apply, hT, hg']
      exact hL.1 f g
  have hne : ℓ₀ ≠ 0 := by
    obtain ⟨f, hf⟩ := hNorm
    obtain ⟨g', hg'⟩ := hpre f
    have hm := (hMatch hg' 1).1
    intro hzero
    rw [hf, hzero] at hm
    exact zero_ne_one hm
  have he : realRank e = r + 1 := (realRank_ascendingExpand d).trans hd
  obtain ⟨c, hc⟩ := hasSmoothWhittakerUniqueness_of_map_character (r := r) (ascendingCharacters d)
    he a ℓ₀ ℓ hBound₀ hBound hCov₀ hCov₁ hne
  refine ⟨c, LinearMap.ext fun f => funext fun g => ?_⟩
  obtain ⟨g', hg'⟩ := hpre f
  have hm := hMatch hg' g
  change B f g = c * B₀ f g
  rw [← hm.1, ← hm.2, hc]
  rfl

/-- Given smooth Casselman–Wallach extension, a normalized uniform map spans
all uniform coefficient maps of the same irreducible real standard module. -/
def RealUniformWhittakerMultiplicityOneFromSmoothExtensionStatement : Prop :=
  RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0} →
    ∀ (m : ℕ) (d : List RealBlock) (a : ℝˣ), realRank d = m + 1 →
      IsIrreducibleGKModule (realStandardRep (m + 1) d) (realStandardLie (m + 1) d) →
    ∀ (B₀ B : Automorphic.realStandardKFinite (m + 1) d →ₗ[ℂ]
      (Langlands.GeneralLinear (m + 1) ℝ → ℂ)),
      IsRealUniformWhittakerIntertwiner m d a B₀ → IsRealUniformWhittakerIntertwiner m d a B →
      (∃ f, B₀ f 1 = 1) → ∃ c : ℂ, B = c • B₀

theorem realUniformWhittakerMultiplicityOneFromSmoothExtension :
    RealUniformWhittakerMultiplicityOneFromSmoothExtensionStatement :=
  fun hCW _ d a hd hIrr B₀ B hB₀ hB hNorm =>
    exists_smul_of_normalized_realUniformIntertwiner hCW d hd a hIrr B₀ B hB₀ hB hNorm

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
