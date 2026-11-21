import Langlands.Global.RankinSelberg.RealGodementCanonicalNonzero
import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerUniqueness

/-! # Comparison with the canonical real Jacquet evaluation -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealGodement RealGodementProfiles RealJacquetFrobenius
open RealPrincipalSeriesDistribution

private theorem charData_parity_exponent (d : RealCharacterData) : charData d.parity d.exponent = d := by
  obtain ⟨χ, p, z, hχ⟩ := d
  have h : charHom p z = χ := by
    apply ContinuousMonoidHom.ext
    intro x
    apply Units.ext
    exact (hχ x).symm
  cases h
  rfl

/-- Every list of real characters of the indicated rank is a spectral character list. -/
theorem exists_characterList_of_map_character {n : ℕ} (cs : List RealCharacterData)
    (h : realRank (cs.map RealBlock.character) = n) :
    ∃ (p : Fin n → Fin 2) (z : Fin n → ℂ), cs.map RealBlock.character = characterList p z := by
  have hn : cs.length = n := (realRank_map_character cs).symm.trans h
  let c (i : Fin n) : RealCharacterData := cs.get (i.cast hn.symm)
  refine ⟨fun i => (c i).parity, fun i => (c i).exponent, ?_⟩
  have he : (fun i => charData (c i).parity (c i).exponent) = c :=
    funext fun i => charData_parity_exponent (c i)
  have hcs : List.ofFn c = cs := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hn.symm
    · intro i hi hj
      rw [List.getElem_ofFn]
      rfl
  rw [characterList, he, hcs]

private def normalizedExponentVector {n : ℕ} (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => z i + ((n : ℂ) - 1) / 2 - (i.val : ℂ)

private theorem normalizedCharacterBlocks_eq_characterList {n : ℕ} (p : Fin n → Fin 2) (z : Fin n → ℂ) :
    normalizedCharacterBlocks (normalizedExponentVector z) p = characterList p z := by
  have h : chars (normalizedExponentVector z) p = fun i => charData (p i) (z i) := by
    funext i
    unfold chars expo normalizedExponentVector
    congr 1
    ring
  rw [normalizedCharacterBlocks, characterList, h]

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation:max "P" ds:max => principalSeries ℝ (r + 1) (realPositionCharacter ds)

/-- Equivariance of a linear form for the standard real upper-unipotent character. -/
def HasWhittakerCovariance (ds : List RealBlock) (a : ℝˣ) (ℓ : P ds →ₗ[ℂ] ℂ) : Prop :=
  ∀ (u : N) (f : P ds), ℓ (translate r ds u.val f) = realWhittakerCharacter a u.val * ℓ f

/-- Whittaker uniqueness for a position character list. -/
def HasSmoothWhittakerUniqueness (r : ℕ) (ds : List RealBlock) (a : ℝˣ) : Prop :=
  ∀ ℓ₁ ℓ₂ : principalSeries ℝ (r + 1) (realPositionCharacter ds) →ₗ[ℂ] ℂ,
    HasCompactDerivativeBound r ds ℓ₁ → HasCompactDerivativeBound r ds ℓ₂ →
    HasWhittakerCovariance ds a ℓ₁ → HasWhittakerCovariance ds a ℓ₂ → ℓ₁ ≠ 0 →
    ∃ c : ℂ, ℓ₂ = c • ℓ₁

theorem hasSmoothWhittakerUniqueness_characterList (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ)
    (a : ℝˣ) : HasSmoothWhittakerUniqueness r (characterList p z) a := by
  rw [← normalizedCharacterBlocks_eq_characterList p z]
  exact RealPrincipalSeriesWhittakerUniqueness.exists_smul_of_whittakerFunctional (normalizedExponentVector z) p a

theorem hasSmoothWhittakerUniqueness_of_map_character (cs : List RealCharacterData)
    (hr : realRank (cs.map RealBlock.character) = r + 1) (a : ℝˣ) :
    HasSmoothWhittakerUniqueness r (cs.map RealBlock.character) a := by
  obtain ⟨p, z, he⟩ := exists_characterList_of_map_character cs hr
  rw [he]
  exact hasSmoothWhittakerUniqueness_characterList p z a

variable (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ)
local notation "ds" => characterList p z

/-- A compact-derivative-bounded smooth evaluation giving the canonical coefficients. -/
def HasBoundedCanonicalEvaluation : Prop :=
  ∃ ℓ : P ds →ₗ[ℂ] ℂ, HasCompactDerivativeBound r ds ℓ ∧
    HasWhittakerCovariance ds (-a) ℓ ∧ functionalCoefficient ds ℓ = canonicalJacquetMap a p z

/-- In the dominant chamber the convergent open-cell integral supplies the bounded evaluation. -/
theorem hasBoundedCanonicalEvaluation_of_chamber (hz : z ∈ realSpectralChamber r) :
    HasBoundedCanonicalEvaluation a p z := by
  have hDom := isStrictlyDominant_characterList p hz
  let ℓ := additiveJacquetForm a hDom
  refine ⟨ℓ, hasCompactDerivativeBound_additiveJacquetForm a hDom, ?_, ?_⟩
  · intro u f
    change additiveJacquetIntegral a (fun g => f.val (g * u.val)) 1 =
      realWhittakerCharacter (-a) u.val * additiveJacquetIntegral a f.val 1
    rw [additiveJacquetIntegral_rightTranslate, one_mul]
    simpa only [mul_one] using realGodementOpenCellCovariance r a f.val u 1
  · ext1 f
    exact (additiveJacquetUniformLinear_apply a hDom f).trans (canonicalJacquetMap_agrees a p hz f).symm

/-- Every bounded smooth Whittaker form gives a scalar multiple of the
canonical coefficients whenever the canonical evaluation has a compact derivative bound. -/
theorem functionalCoefficient_eq_smul_canonical (h : HasBoundedCanonicalEvaluation a p z)
    (L : P ds →ₗ[ℂ] ℂ) (hL : HasCompactDerivativeBound r ds L)
    (hψ : HasWhittakerCovariance ds (-a) L) :
    ∃ c : ℂ, functionalCoefficient ds L = c • canonicalJacquetMap a p z := by
  obtain ⟨ℓ, hb, hχ, hEq⟩ := h
  have hne : ℓ ≠ 0 := by
    intro he
    apply canonicalJacquetMap_ne_zero r a p z
    rw [← hEq, he]
    ext1 f
    funext g
    rfl
  obtain ⟨c, rfl⟩ := hasSmoothWhittakerUniqueness_characterList p z (-a) ℓ L hb hL hχ hψ hne
  refine ⟨c, ?_⟩
  rw [← hEq]
  ext1 f
  funext g
  rfl

/-- In the dominant chamber, bounded Whittaker evaluation has exactly the
canonical coefficient line, with scalar independent of the vector. -/
def RealCanonicalWhittakerComparisonStatement : Prop :=
  ∀ (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ),
    z ∈ realSpectralChamber r →
    ∀ L : principalSeries ℝ (r + 1) (realPositionCharacter (characterList p z)) →ₗ[ℂ] ℂ,
      HasCompactDerivativeBound r (characterList p z) L →
      HasWhittakerCovariance (characterList p z) (-a) L →
      ∃ c : ℂ, functionalCoefficient (characterList p z) L = c • canonicalJacquetMap a p z

theorem realCanonicalWhittakerComparison : RealCanonicalWhittakerComparisonStatement := by
  intro r a p z hz
  exact functionalCoefficient_eq_smul_canonical a p z (hasBoundedCanonicalEvaluation_of_chamber a p z hz)

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
