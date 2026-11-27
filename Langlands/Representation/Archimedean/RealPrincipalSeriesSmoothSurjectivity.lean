import Langlands.Representation.Archimedean.SmoothCasselmanWallachPrincipalSeries
import Langlands.Representation.Archimedean.RealSmoothQuotientWordLift
import Langlands.Representation.Archimedean.SmoothDerivativeOpenMapping

/-! # Smooth surjectivity and controlled lifts of principal-series quotients -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open DerivativeSmoothVectors

universe uV uE uE₁ uE₂

local notation "I" n:max => matrixModel ℝ n
local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "blocks" cs:max => List.map RealBlock.character cs
local notation "P" n:max cs:max => kFiniteFunctions (realStandardModule n (blocks cs)) (unitaryCompact ℝ n)
local notation "R₀" rank:max cs:max =>
  RealStandardCompactBanach.representation (n := rank) (blocks cs)
local notation "j" rank:max cs:max =>
  RealStandardCompactBanach.compactFiniteEquiv (n := rank) (blocks cs)

/-- An algebraic principal-series quotient onto the compact-finite module of an irreducible
Banach realization extends to a surjection between the genuine smooth carriers. -/
def RealPrincipalSeriesSmoothSurjectivityStatement : Prop :=
  ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (K (r + 1)) V)
    (π : (ℂ ⊗[ℝ] (M (r + 1))) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G (r + 1) →* (E →L[ℂ] E)) (e : V ≃ₗ[ℂ] smoothKFinite ℝ (r + 1) R)
    (cs : List RealCharacterData) (B : P (r + 1) cs →ₗ[ℂ] V),
    IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ → IsContinuousRepresentation R →
    IsSmoothGKIntertwiner ℝ (r + 1) R ρ π
      ((smoothKFinite ℝ (r + 1) R).subtype.comp e.toLinearMap) →
    cs.length = r + 1 → IsRealStandardIntertwiner (r + 1) ρ π (blocks cs) B →
    Function.Surjective B →
    ∃ Q : DerivativeSmoothVectors (I (r + 1)) (R₀ (r + 1) cs) →L[ℂ]
        DerivativeSmoothVectors (I (r + 1)) R,
      Function.Surjective Q ∧
      (∀ g x, Q (representation (I (r + 1)) (R₀ (r + 1) cs) g x) =
        representation (I (r + 1)) R g (Q x)) ∧
      ∀ w : P (r + 1) cs, Q ((j (r + 1) cs) w) = e (B w)

/-- Smooth surjectivity and the compact-finite comparison give the controlled lift
through a principal-series quotient. -/
theorem realPrincipalSeriesQuotientWordLift_of_smoothSurjectivity
    (h : RealPrincipalSeriesSmoothSurjectivityStatement.{uV, uE}) :
    RealPrincipalSeriesQuotientWordLiftStatement.{uV, uE} := by
  intro r V _ _ ρ π E _ _ _ R e cs B hirr hadm hR he hcs hB hBsurj J
  let n := r + 1
  let R' := R₀ n cs
  let j' := j n cs
  obtain ⟨Q, hQ, hQG, hQe⟩ := h r V ρ π E R e cs B hirr hadm hR he hcs hB hBsurj
  have hR' : IsContinuousRepresentation R' :=
    RealStandardCompactBanach.isContinuousRepresentation (blocks cs)
  have hopen : IsOpenMap Q := isOpenMap_of_surjective_units hR' hR Q hQ
  have hsurj (y : DerivativeSmoothVectors (I n) R) (hy : y ∈ smoothKFinite ℝ n R) :
      ∃ x ∈ smoothKFinite ℝ n R', Q x = y := by
    obtain ⟨v, hv⟩ := e.surjective ⟨y, hy⟩
    obtain ⟨w, hw⟩ := hBsurj v
    have hew : e (B w) = ⟨y, hy⟩ := by rw [hw, hv]
    exact ⟨j' w, (j' w).prop, (hQe w).trans (congrArg Subtype.val hew)⟩
  obtain ⟨T, C, hC, hT⟩ := realSmoothQuotientWordLift R' R Q hR' hopen
    (fun k x => hQG (Unitary.toUnits k) x) hsurj J
  refine ⟨T, C, hC, fun v => ?_⟩
  obtain ⟨x, hx, hQx, hb⟩ := hT (e v) (e v).prop
  obtain ⟨w, hw⟩ := j'.surjective ⟨x, hx⟩
  have hwx : ((j' w : smoothKFinite ℝ n R') : DerivativeSmoothVectors (I n) R') = x :=
    congrArg Subtype.val hw
  refine ⟨w, e.injective (Subtype.ext ?_), ?_⟩
  · rw [← hQe, hwx, hQx]
  · change (∑ Xs ∈ J, ‖derivativeCLM (I n) R' Xs
        (j' w : DerivativeSmoothVectors (I n) R')‖) ≤
        C * ∑ Ys ∈ T, ‖derivativeCLM (I n) R Ys (e v : DerivativeSmoothVectors (I n) R)‖
    rwa [hwx]

/-- The principal-series bound and the smooth quotient theorem together imply the general
finite-word bound with the original independent carrier universes. -/
theorem realSmoothCasselmanWallachBound_of_principalSeries_surjectivity
    (hB : RealPrincipalSeriesWordBoundStatement.{uE₂})
    (hS : RealPrincipalSeriesSmoothSurjectivityStatement.{uV, uE₁}) :
    RealSmoothCasselmanWallachBoundStatement.{uV, uE₁, uE₂} :=
  realSmoothCasselmanWallachBound_of_principalSeries hB
    (realPrincipalSeriesQuotientWordLift_of_smoothSurjectivity hS)

end Langlands.Archimedean
