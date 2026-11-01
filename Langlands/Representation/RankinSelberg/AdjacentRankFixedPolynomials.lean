import Langlands.Representation.RankinSelberg.AdjacentRankCertifiedRealRay
import Langlands.Representation.RankinSelberg.AdjacentRankUpperFamilyTransport
import Langlands.Representation.RankinSelberg.AdjacentRankClearingKernel

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fixedPolynomialTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fixedPolynomialValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance fixedPolynomialLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance fixedPolynomialT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance fixedPolynomialTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance fixedPolynomialMeasurable : MeasurableSpace F.Carrier := borel _
local instance fixedPolynomialBorel : BorelSpace F.Carrier := ⟨rfl⟩

/-- The predecessor sizes of the actual lower adjacent-rank pair. -/
theorem adjacentLowerPair_sum (r : ℕ) :
    ∑ i : Fin 2, (![r, 0] i + 1) = (r + 1) + 1 := by simp

/-- The lower pair on the original first carrier and the lifted scalar carrier. -/
def adjacentLowerPairBlocks {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (i : Fin 2) :
    Representation ℂ (Langlands.GeneralLinear (![r, 0] i + 1) F.Carrier)
      (Shahidi.pairCarrier V (ULift.{uV} ℂ) i) :=
  match i with
  | 0 => σ
  | 1 => rankOneExtensionCharacter.{uF, uV} F χ

/-- Transport an ordered lower family across equal sizes and equal block actions. -/
def oppositeInducedEquiv_of_sizes
    {t : ℕ} (B : BlockShape (t + 1)) (m : Fin B.length → ℕ)
    (hsize : ∀ i, B.size i = m i + 1)
    (h : ∑ i, (m i + 1) = t + 1)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (B.size i) F.Carrier) (V i))
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))
    (heq : ∀ i, (hsize i ▸ σ i) = τ i) :
    (F.canonicalNormalizedOppositeParabolicInduced B (B.blockTensor σ)).Equiv
      (F.canonicalNormalizedOppositeParabolicInduced (succBlockShape m h)
        ((succBlockShape m h).blockTensor τ)) := by
  cases B with
  | mk k size hpos hsum =>
    dsimp only at m hsize h V σ τ heq ⊢
    have hs : size = fun i => m i + 1 := funext hsize
    subst size
    have hστ : σ = τ := funext heq
    subst τ
    exact Representation.Equiv.refl _

set_option backward.isDefEq.respectTransparency false in
/-- The literal determinant-power twist is exactly the real spectral
quasicharacter twist on the lifted scalar representation. -/
theorem rankOneExtensionCharacter_realTwisted (χ : Quasicharacter F.Carrier) (u : ℝ) :
    Langlands.twist (F.canonicalTopologicalData.determinantComplexPower 1 (u : ℂ))
      (rankOneExtensionCharacter.{uF,uV} F χ) =
    rankOneExtensionCharacter.{uF,uV} F (AdjacentCompactMatrix.realTwistedCharacter F χ u) := by
  ext g v
  change (F.canonicalTopologicalData.determinantComplexPower 1 (u : ℂ) g : ℂ) *
    ((χ (determinant g) : ℂ) * v.down) =
    ((AdjacentCompactMatrix.realTwistedCharacter F χ u (determinant g) : ℂ) * v.down)
  change (F.canonicalTopologicalData.unramifiedCharacter _ (determinant g) : ℂ) *
    ((χ (determinant g) : ℂ) * v.down) =
    ((χ (determinant g) : ℂ) *
      (F.canonicalTopologicalData.unramifiedCharacter _ (determinant g) : ℂ)) * v.down
  ring

/-- The large-second-twist lower model is the actual ordered second-block
deformation, preserving the original first carrier and the lifted scalar carrier. -/
def adjacentLowerPair_realTwistEquiv {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (u : ℝ) :
    (F.canonicalNormalizedOppositeParabolicInduced
      (Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0))
      ((Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF,uV} F
          (AdjacentCompactMatrix.realTwistedCharacter F χ u))))).Equiv
      (twoBlockSecondDeformedInduced F ![r, 0] (adjacentLowerPair_sum r)
        (adjacentLowerPairBlocks F σ χ) (u : ℂ)) := by
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  have hsize : ∀ i : Fin 2, B.size i = ![r, 0] i + 1 := by
    intro i
    fin_cases i <;> rfl
  apply oppositeInducedEquiv_of_sizes F B ![r, 0] hsize (adjacentLowerPair_sum r)
    (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF,uV} F
      (AdjacentCompactMatrix.realTwistedCharacter F χ u)))
    (twoBlockSecondDeformedBlocks F ![r, 0] (adjacentLowerPairBlocks F σ χ) (u : ℂ))
  intro i
  fin_cases i
  · change σ = Langlands.twist (F.canonicalTopologicalData.determinantComplexPower
      (r + 1) 0) σ
    simp only [PadicField.TopologicalData.determinantComplexPower_zero, twist_one]
  · change rankOneExtensionCharacter.{uF,uV} F
      (AdjacentCompactMatrix.realTwistedCharacter F χ u) =
      Langlands.twist (F.canonicalTopologicalData.determinantComplexPower 1 (u : ℂ))
        (rankOneExtensionCharacter.{uF,uV} F χ)
    exact (rankOneExtensionCharacter_realTwisted F χ u).symm

/-- Fixed complete block certificates and actual induced certificates on one
real ray, with the second block polynomial rescaled by the spectral point. -/
def AdjacentLowerPairFixedRealRayCertificates
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (χ : Quasicharacter F.Carrier) : Prop :=
  ∃ (P₀ P₁ : Polynomial ℂ) (C : ℝ),
    IsPadicSymmetricLPolynomial F ψ μ τ σ P₀ ∧
    IsPadicSymmetricLPolynomial F ψ μ τ (rankOneExtensionCharacter.{uF,uV} F χ) P₁ ∧
    SecondBlockCorankRealRayCertificates F ψ μ ![r, 0] (adjacentLowerPair_sum r)
      (adjacentLowerPairBlocks F σ χ) τ P₀ P₁ C

/-- Complete certificate existence, uniqueness and unramified transport fix the
two block polynomials in the actual large-second-twist divisibility theorem. -/
theorem adjacentLowerPair_fixedRealRayCertificates
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (χ : Quasicharacter F.Carrier) :
    AdjacentLowerPairFixedRealRayCertificates F ψ μ σ τ χ := by
  let μsd : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨μ, hself⟩
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists p F ψ μsd r r W V τ σ hτ hσ
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists p F ψ μsd r 0 W (ULift.{uV} ℂ)
    τ (rankOneExtensionCharacter.{uF,uV} F χ) hτ
    (rankOneExtensionCharacter_isOfWhittakerType F ψ χ)
  obtain ⟨C, hC⟩ := adjacentRankLargeTwistLDivisibility F ψ μ hself σ τ hσ hτ χ
  refine ⟨P₀, P₁, C, hP₀, hP₁, ?_⟩
  intro u hu
  obtain ⟨P, P₀u, P₁u, hP, hP₀u, hP₁u, Q, e, hdiv⟩ := hC u hu
  have h₀ : P₀u = P₀ := hP₀u.unique hP₀
  have hP₁twist := symmetricLPolynomial_determinantComplexPower F ψ μsd τ
    (rankOneExtensionCharacter.{uF,uV} F χ) (u : ℂ) P₁ hP₁
  rw [rankOneExtensionCharacter_realTwisted F χ u] at hP₁twist
  have h₁ : P₁u = P₁.comp (Polynomial.C
      (spectralPoint F.canonicalTopologicalData.residueCardinality (u : ℂ)) *
        Polynomial.X) := hP₁u.unique hP₁twist
  refine ⟨P, ?_, Q, e, ?_⟩
  · exact (IsPadicSymmetricLPolynomial.congr_equiv
      (adjacentLowerPair_realTwistEquiv F σ χ u) (Representation.Equiv.refl τ)).mp
      ((isPadicSymmetricLPolynomial_comm F ψ μ _ τ P).mpr hP)
  · simpa only [h₀, h₁] using hdiv

end Langlands.RankinSelberg.Padic
