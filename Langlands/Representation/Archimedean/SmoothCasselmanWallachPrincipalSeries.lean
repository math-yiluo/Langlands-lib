import Langlands.Representation.Archimedean.SmoothCasselmanWallachBound
import Langlands.Representation.Archimedean.RealSmoothGKModule
import Langlands.Representation.Archimedean.GKModuleQuotient
import Langlands.Representation.Archimedean.RealPrincipalSeriesQuotientProof
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction
import Langlands.Global.RankinSelberg.RealStandardCompactFinite

/-! # Word estimates along principal-series quotients -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV uE uE₁ uE₂

open DerivativeSmoothVectors
open Langlands.Global.RankinSelbergGlobal

local notation "I" n:max => matrixModel ℝ n
local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "L" n:max => ℂ ⊗[ℝ] (M n)
local notation "blocks" cs:max => List.map RealBlock.character cs
local notation "P" n:max cs:max => kFiniteFunctions (realStandardModule n (blocks cs)) (unitaryCompact ℝ n)
local notation "R₀" rank:max cs:max =>
  RealStandardCompactBanach.representation (n := rank) (blocks cs)
local notation "j" rank:max cs:max =>
  RealStandardCompactBanach.compactFiniteEquiv (n := rank) (blocks cs)

/-- A map from the compact-finite scalar minimal principal series to genuine smooth Banach
vectors that preserves the compact and derived actions has an underlying norm bound by
finitely many word seminorms in the compact Banach model. -/
def RealPrincipalSeriesWordBoundStatement : Prop :=
  ∀ (r : ℕ) (cs : List RealCharacterData), cs.length = r + 1 →
    ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (R : G (r + 1) →* (E →L[ℂ] E))
      (f : P (r + 1) cs →ₗ[ℂ] DerivativeSmoothVectors (I (r + 1)) R),
      IsContinuousRepresentation R →
      IsSmoothGKIntertwiner ℝ (r + 1) R (realStandardRep (r + 1) (blocks cs))
        (realStandardLie (r + 1) (blocks cs)) f →
      ∃ (S : Finset (List (M (r + 1)))) (C : ℝ), 0 ≤ C ∧
        ∀ w : P (r + 1) cs,
          ‖derivativeCLM (I (r + 1)) R [] (f w)‖ ≤
            C * ∑ Xs ∈ S, ‖derivativeCLM (I (r + 1)) (R₀ (r + 1) cs) Xs
              ((j (r + 1) cs) w : DerivativeSmoothVectors (I (r + 1)) (R₀ (r + 1) cs))‖

/-- Finite-word control on compact-finite lifts through a scalar minimal principal-series
quotient onto the compact-finite genuine smooth vectors of an irreducible Banach realization. -/
def RealPrincipalSeriesQuotientWordLiftStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (K (r + 1)) V) (π : (L (r + 1)) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G (r + 1) →* (E →L[ℂ] E)) (e : V ≃ₗ[ℂ] smoothKFinite ℝ (r + 1) R)
    (cs : List RealCharacterData) (B : P (r + 1) cs →ₗ[ℂ] V),
    IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ → IsContinuousRepresentation R →
    IsSmoothGKIntertwiner ℝ (r + 1) R ρ π
      ((smoothKFinite ℝ (r + 1) R).subtype.comp e.toLinearMap) →
    cs.length = r + 1 → IsRealStandardIntertwiner (r + 1) ρ π (blocks cs) B →
    Function.Surjective B →
    ∀ S : Finset (List (M (r + 1))),
      ∃ (T : Finset (List (M (r + 1)))) (D : ℝ), 0 ≤ D ∧
        ∀ v : V, ∃ w : P (r + 1) cs, B w = v ∧
          (∑ Xs ∈ S, ‖derivativeCLM (I (r + 1)) (R₀ (r + 1) cs) Xs
            ((j (r + 1) cs) w : DerivativeSmoothVectors (I (r + 1)) (R₀ (r + 1) cs))‖) ≤
            D * ∑ Ys ∈ T, ‖derivativeCLM (I (r + 1)) R Ys
              (e v : DerivativeSmoothVectors (I (r + 1)) R)‖

section Transport

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (K n) V} {π : (L n) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : G n →* (E →L[ℂ] E)}

/-- Transport the real Harish-Chandra module compatibility across a genuine compact-finite
realization. -/
theorem isRealGKModule_of_smoothKFiniteEquiv (hR : IsContinuousRepresentation R)
    (e : V ≃ₗ[ℂ] smoothKFinite ℝ n R)
    (he : IsSmoothGKIntertwiner ℝ n R ρ π
      ((smoothKFinite ℝ n R).subtype.comp e.toLinearMap)) : IsRealGKModule n ρ π := by
  let σ := smoothKFiniteRepresentation ℝ n R
  let ψ := RealSmoothGK.lieAction n R hR
  have hc (k : K n) (v : V) : e (ρ k v) = σ k (e v) := Subtype.ext (he.1 k v)
  have hreal (X : M n) (v : V) : e (π (1 ⊗ₜ[ℝ] X) v) = ψ (1 ⊗ₜ[ℝ] X) (e v) := by
    apply Subtype.ext
    rw [RealSmoothGK.lieAction_one_tmul]
    exact he.2 X v
  have hℓ (X : L n) (v : V) : e (π X v) = ψ X (e v) := by
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      have h : (c ⊗ₜ[ℝ] X : L n) = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul, LinearMap.smul_apply, map_smul, hreal, map_smul, LinearMap.smul_apply]
    | add X Y hX hY =>
      rw [map_add, LinearMap.add_apply, map_add, hX, hY, map_add, LinearMap.add_apply]
  let A : σ.IntertwiningMap ρ :=
    e.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap σ ρ fun k w => by
      apply e.injective
      simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        (hc k (e.symm w)).symm
  refine (RealSmoothGK.isRealGKModule n R hR).of_surjective A e.symm.surjective ?_
  intro X w
  change e.symm (ψ X w) = π X (e.symm w)
  apply e.injective
  simpa only [LinearEquiv.apply_symm_apply] using (hℓ X (e.symm w)).symm

end Transport

/-- The two principal-series estimates imply the Casselman–Wallach word-seminorm bound
through Casselman's algebraic quotient presentation. -/
theorem realSmoothCasselmanWallachBound_of_principalSeries
    (hbound : RealPrincipalSeriesWordBoundStatement.{uE₂})
    (hlift : RealPrincipalSeriesQuotientWordLiftStatement.{uV, uE₁}) :
    RealSmoothCasselmanWallachBoundStatement.{uV, uE₁, uE₂} := by
  intro r V _ _ ρ π E₁ _ _ _ R₁ E₂ _ _ _ R₂ e f hirr hadm hR₁ hR₂ he hf
  have hGK := isRealGKModule_of_smoothKFiniteEquiv hR₁ e he
  obtain ⟨cs, hcs, B, hB₀, hB⟩ := realPrincipalSeriesQuotient (r + 1) V ρ π hGK hirr hadm
  have hcomp : IsSmoothGKIntertwiner ℝ (r + 1) R₂ (realStandardRep (r + 1) (blocks cs))
      (realStandardLie (r + 1) (blocks cs)) (f.comp B) := by
    constructor
    · intro k w
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hB.map_realStandardRep, hf.1]
    · intro X w
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hB.map_realStandardLie, hf.2]
  obtain ⟨S, C, hC, hS⟩ := hbound r cs hcs E₂ R₂ (f.comp B) hR₂ hcomp
  obtain ⟨T, D, -, hT⟩ := hlift r V ρ π E₁ R₁ e cs B hirr hadm hR₁ he hcs hB
    (hB.surjective hirr hB₀) S
  refine ⟨T, C * D, fun v => ?_⟩
  obtain ⟨w, hw, hwT⟩ := hT v
  have h := (hS w).trans (mul_le_mul_of_nonneg_left hwT hC)
  simpa only [LinearMap.comp_apply, hw, mul_assoc] using h

end Langlands.Archimedean
