import Langlands.Representation.Parabolic.OppositeInducedMapSurjectivity
import Langlands.Representation.Whittaker.SurjectiveCoefficientTransport
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof
import Langlands.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.Representation.Shahidi.Induction

/-! # Original-carrier transport for the adjacent-rank lower induction -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The lifted rank-one character has the same action in any two carrier universes. -/
def rankOneExtensionCharacterUniverseEquiv
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier) :
    (rankOneExtensionCharacter.{uF, uV} F χ).Equiv
      (rankOneExtensionCharacter.{uF, uW} F χ) :=
  Representation.Equiv.mk
    ((ULift.moduleEquiv : ULift.{uV} ℂ ≃ₗ[ℂ] ℂ).trans
      (ULift.moduleEquiv : ULift.{uW} ℂ ≃ₗ[ℂ] ℂ).symm)
    (by intro g; rfl)

variable (ψ : letI := F.canonicalTopologicalData.topology;
  UnitaryAdditiveCharacter F.Carrier)
variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
variable (ℓ : letI := F.canonicalTopologicalData.topology; glFunctionals ψ r σ)
variable (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)

/-- The two actual factor maps: the surjection onto the specified coefficient
image and the harmless change of universe in the rank-one scalar carrier. -/
def adjacentCoefficientFactorMap (i : Fin 2) :
    letI := F.canonicalTopologicalData.topology
    (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ) i).IntertwiningMap
      (Shahidi.pairFamily (V₁ := (glCoefficientModel ψ r σ ℓ).toSubmodule)
        (glModelRepresentation ψ r σ ℓ)
        (rankOneExtensionCharacter.{uF, uF} F χ) i) :=
  match i with
  | 0 => modelMap σ ℓ
  | 1 => (rankOneExtensionCharacterUniverseEquiv.{uF, uV, uF} F χ).toIntertwiningMap

theorem adjacentCoefficientFactorMap_surjective (i : Fin 2) :
    letI := F.canonicalTopologicalData.topology
    Function.Surjective (adjacentCoefficientFactorMap F ψ σ ℓ χ i) := by
  fin_cases i
  · exact modelMap_surjective σ ℓ
  · exact (rankOneExtensionCharacterUniverseEquiv.{uF, uV, uF} F χ).toLinearEquiv.surjective

/-- The canonical model-side lower induction, with the same ordered blocks
`(r+1,1)` and a scalar carrier in the coefficient model's universe. -/
abbrev adjacentCoefficientInducedRepresentation :
    letI := F.canonicalTopologicalData.topology
    Representation ℂ (GeneralLinear (r + 2) F.Carrier)
      (let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
       (F.canonicalNormalizedOppositeParabolicInduced B
         (B.blockTensor (Shahidi.pairFamily (V₁ := (glCoefficientModel ψ r σ ℓ).toSubmodule)
           (glModelRepresentation ψ r σ ℓ)
           (rankOneExtensionCharacter.{uF, uF} F χ)))).asModule) :=
  letI := F.canonicalTopologicalData.topology
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  F.canonicalNormalizedOppositeParabolicInduced B
    (B.blockTensor (Shahidi.pairFamily (V₁ := (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (glModelRepresentation ψ r σ ℓ)
      (rankOneExtensionCharacter.{uF, uF} F χ)))

/-- The actual original-carrier lower induction maps onto the model-side
lower induction by postcomposition with the external tensor of the factor maps. -/
def adjacentCoefficientInducedMap :
    letI := F.canonicalTopologicalData.topology
    let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
    (F.canonicalNormalizedOppositeParabolicInduced B
      (B.blockTensor (Shahidi.pairFamily σ
        (rankOneExtensionCharacter.{uF, uV} F χ)))).IntertwiningMap
      (adjacentCoefficientInducedRepresentation F ψ σ ℓ χ) :=
  letI := F.canonicalTopologicalData.topology
  F.canonicalTopologicalData.normalizedOppositeParabolicInducedMap _
    (FiniteTensor.externalMap (adjacentCoefficientFactorMap F ψ σ ℓ χ))

/-- The coefficient-image transport of the actual lower induction is surjective.
Smoothness of the original representation suffices; injectivity and
irreducibility are not required. -/
theorem adjacentCoefficientInducedMap_surjective
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ) :
    letI := F.canonicalTopologicalData.topology
    Function.Surjective (adjacentCoefficientInducedMap F ψ σ ℓ χ) := by
  let := F.canonicalTopologicalData.topology
  apply F.canonicalTopologicalData.normalizedOppositeParabolicInducedMap_surjective
  · apply FiniteTensor.isSmooth_external
    intro i
    fin_cases i
    · exact hσ
    · exact rankOneExtensionCharacter_isSmooth F ψ χ
  · apply FiniteTensor.isSmooth_external
    intro i
    fin_cases i
    · exact glModel_isSmooth ψ r σ hσ ℓ
    · exact rankOneExtensionCharacter_isSmooth F ψ χ
  · exact FiniteTensor.externalMapSurjectivity ℂ _ _ _ _ _ _
      (adjacentCoefficientFactorMap F ψ σ ℓ χ)
      (adjacentCoefficientFactorMap_surjective F ψ σ ℓ χ)

/-- A nonzero model-side functional realizing an entire function image yields
a nonzero functional with the same image on the exact original-carrier
induction. The witness is its pullback along `adjacentCoefficientInducedMap`. -/
theorem adjacentCoefficientInducedImage_transport
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ)
    (S : Set (GeneralLinear (r + 2) F.Carrier → ℂ))
    (J : letI := F.canonicalTopologicalData.topology
      glFunctionals ψ (r + 1) (adjacentCoefficientInducedRepresentation F ψ σ ℓ χ))
    (hJ : J.val ≠ 0)
    (hS : letI := F.canonicalTopologicalData.topology
      S = Set.range (fun v : (adjacentCoefficientInducedRepresentation F ψ σ ℓ χ).asModule =>
        fun g => J.val (adjacentCoefficientInducedRepresentation F ψ σ ℓ χ g v))) :
    letI := F.canonicalTopologicalData.topology
    let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
    let ρ := F.canonicalNormalizedOppositeParabolicInduced B
      (B.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))
    ∃ J₀ : glFunctionals ψ (r + 1) ρ, J₀.val ≠ 0 ∧
      S = Set.range (fun v : ρ.asModule => fun g => J₀.val (ρ g v)) := by
  let := F.canonicalTopologicalData.topology
  let q := adjacentCoefficientInducedMap F ψ σ ℓ χ
  have hq : Function.Surjective q := adjacentCoefficientInducedMap_surjective F ψ σ ℓ χ hσ
  refine ⟨functionalsComap q J, functionalsComap_ne_zero q hq J hJ, ?_⟩
  exact hS.trans (coefficientRange_functionalsComap q hq J).symm

end Langlands.RankinSelberg
