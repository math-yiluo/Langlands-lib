import Langlands.Global.RankinSelberg.RealCanonicalWhittakerComparison
import Langlands.Global.RankinSelberg.RealPrincipalSeriesSmoothQuotient

/-! # Smooth evaluation on ascending real character presentations -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors RealGodement RealGodementProfiles
open RealStrictCharacterLanglandsQuotient RealPrincipalSeries

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation:max "S" ds:max => realStandardModule (r + 1) ds
local notation:max "R" ds:max => representation (n := r + 1) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation:max "V" ds:max => Automorphic.realStandardKFinite (r + 1) ds
local notation:max "P" ds:max => principalSeries ℝ (r + 1) (realPositionCharacter ds)
local notation:max "act" ds:max => DerivativeSmoothVectors.representation I (R ds)

private theorem isCharacterList_map_character (cs : List RealCharacterData) :
    IsCharacterList (cs.map RealBlock.character) := by
  intro b hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨c, rfl⟩

private def positionToStandard (ds : List RealBlock) (hds : IsCharacterList ds) : P ds →ₗ[ℂ] S ds :=
  Submodule.inclusion (realStandardModule_eq hds).ge

/-- On a character list, a continuous Whittaker evaluation of genuine smooth
vectors is a bounded Whittaker form on the full smooth position series. -/
theorem exists_boundedForm_of_characterEvaluation (ds : List RealBlock) (hds : IsCharacterList ds)
    (a : ℝˣ) (L : D ds →L[ℂ] ℂ)
    (hL : ∀ (u : N) (v : D ds), L (act ds u.val v) = realWhittakerCharacter a u.val * L v) :
    ∃ ℓ : P ds →ₗ[ℂ] ℂ, HasCompactDerivativeBound r ds ℓ ∧ HasWhittakerCovariance ds a ℓ ∧
      ∀ (f : V ds) (g : G), functionalCoefficient ds ℓ f g =
        L (act ds g (compactFiniteEquiv ds f).val) := by
  let j := positionToStandard (r := r) ds hds
  let ℓ := L.toLinearMap.comp ((derivativeEquiv ds).toLinearMap.comp j)
  have htranslate (g : G) (F : P ds) : j (RealPrincipalSeries.translate r ds g F) =
      translate ds g (j F) := Subtype.ext rfl
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · obtain ⟨m, Xs, A, hA, hB⟩ := has_compact_bound_of_continuous ds L
    exact ⟨m, Xs, A, hA, fun f b hf => hB (j f) b hf⟩
  · intro u F
    change L (derivativeEquiv ds (j (RealPrincipalSeries.translate r ds u.val F))) =
      realWhittakerCharacter a u.val * L (derivativeEquiv ds (j F))
    rw [htranslate, derivativeEquiv_translate]
    exact hL u _
  · intro f g
    let v : P ds := ⟨f.val, f.property.1.1⟩
    change L (derivativeEquiv ds (j (RealPrincipalSeries.translate r ds g v))) = _
    rw [htranslate, derivativeEquiv_translate, compactFiniteEquiv_val]
    rfl

/-- Given smooth Casselman–Wallach extension, a uniform coefficient of an
irreducible real standard module is a coefficient of one bounded smooth
Whittaker form on the ascending character principal series. -/
def RealAscendingWhittakerEvaluationStatement : Prop :=
  RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0} →
    ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    ∀ (a : ℝˣ) (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
      IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds) →
      IsRealUniformWhittakerIntertwiner r ds a B →
      ∃ ℓ : principalSeries ℝ (r + 1) (realPositionCharacter (ascendingExpand ds)) →ₗ[ℂ] ℂ,
        HasCompactDerivativeBound r (ascendingExpand ds) ℓ ∧ HasWhittakerCovariance (ascendingExpand ds) a ℓ ∧
        ∀ f : Automorphic.realStandardKFinite (r + 1) ds,
          ∃ f' : Automorphic.realStandardKFinite (r + 1) (ascendingExpand ds),
            functionalCoefficient (ascendingExpand ds) ℓ f' = B f

theorem realAscendingWhittakerEvaluation : RealAscendingWhittakerEvaluationStatement := by
  intro hCW r ds hr a B hIrr hB
  obtain ⟨L, hL, _⟩ := realSmoothWhittakerEvaluation hCW r ds a B hIrr hB
  obtain ⟨L', hL'ψ, hL'⟩ := exists_whittakerEvaluation_ascendingExpand ds hr a B L hL
  obtain ⟨ℓ, hℓB, hℓψ, hℓ⟩ := exists_boundedForm_of_characterEvaluation (ascendingExpand ds)
    (isCharacterList_map_character (ascendingCharacters ds)) a L' hL'ψ
  refine ⟨ℓ, hℓB, hℓψ, fun f => ?_⟩
  obtain ⟨f', hf'⟩ := hL' f
  exact ⟨f', funext fun g => (hℓ f' g).trans (hf' g)⟩

/-- Casselman–Wallach extension supplies the compact bound for the canonical
map at irreducible character parameters. -/
theorem hasBoundedCanonicalEvaluation_of_casselmanWallach
    (hCW : RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0})
    (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ)
    (hIrr : IsIrreducibleGKModule (realStandardRep (r + 1) (characterList p z))
      (realStandardLie (r + 1) (characterList p z))) : HasBoundedCanonicalEvaluation a p z := by
  let ds := characterList p z
  obtain ⟨L, hL, _⟩ := realSmoothWhittakerEvaluation hCW r ds (-a) (canonicalJacquetMap a p z) hIrr
    (realGodementCanonicalModel r a p z)
  obtain ⟨ℓ, hℓB, hℓψ, hℓ⟩ := exists_boundedForm_of_characterEvaluation ds
    (isCharacterList_map_character _) (-a) L hL.2
  exact ⟨ℓ, hℓB, hℓψ, LinearMap.ext fun f => funext fun g => (hℓ f g).trans (hL.1 f g)⟩

/-- The original uniform coefficients belong to the canonical image when the
bounded realization of the ascending canonical map is available. -/
theorem exists_canonicalVector_of_ascendingEvaluation
    (hCW : RealSmoothCasselmanWallachExtensionStatement.{0, 0, 0})
    (ds : List RealBlock) (hr : realRank ds = r + 1)
    (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ)
    (hList : ascendingExpand ds = characterList p z) (hCan : HasBoundedCanonicalEvaluation a p z)
    (B : V ds →ₗ[ℂ] (G → ℂ))
    (hIrr : IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds))
    (hB : IsRealUniformWhittakerIntertwiner r ds (-a) B) :
    ∀ f : V ds, ∃ f' : V (characterList p z), canonicalJacquetMap a p z f' = B f := by
  have h := realAscendingWhittakerEvaluation hCW r ds hr (-a) B hIrr hB
  rw [hList] at h
  obtain ⟨ℓ, hℓB, hℓψ, hℓ⟩ := h
  obtain ⟨c, hc⟩ := functionalCoefficient_eq_smul_canonical a p z hCan ℓ hℓB hℓψ
  intro f
  obtain ⟨f', hf'⟩ := hℓ f
  refine ⟨c • f', ?_⟩
  rw [map_smul, ← hf', hc]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
