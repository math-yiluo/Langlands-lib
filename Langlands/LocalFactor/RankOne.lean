import Langlands.Weil.Representation.CharacterLine
import Langlands.Weil.Local.Assembly
import Langlands.ClassFieldTheory.Local.ReciprocityRelations

/-!
# Rank-one inputs on the actual local Weil group

All character transport is conditional on an explicitly supplied reciprocity
candidate. Its geometric normalization is used only with its explicit proof.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.RankOne

open Weil.Local LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Candidate reciprocity for the actual assembled Weil group and canonical topology. -/
abbrev ReciprocityCandidate :=
  WeilReciprocityCandidate F.canonicalTopologicalData (localResidueDegree F)

/-- The actual quotient projection followed by the specified candidate. -/
def reciprocityUnits (e : ReciprocityCandidate F) :
    letI := F.canonicalTopologicalData.topology
    localWeilGroup F →ₜ* F.Carrierˣ := by
  letI := F.canonicalTopologicalData.topology
  exact (e : WeilQuotients.Abelianization (localResidueDegree F) →ₜ* F.Carrierˣ).comp
    (WeilQuotients.projection (localResidueDegree F))

/-- Character transport in the Weil-to-field direction, using actual descent. -/
def fieldCharacter (e : ReciprocityCandidate F) (χ : localWeilGroup F →ₜ* ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    F.Carrierˣ →ₜ* ℂˣ :=
  weilCandidateCharacterEquiv F.canonicalTopologicalData (localResidueDegree F) e χ

/-- Pull a field quasicharacter back through the specified abelianized reciprocity. -/
def weilCharacter (e : ReciprocityCandidate F) :
    letI := F.canonicalTopologicalData.topology
    (F.Carrierˣ →ₜ* ℂˣ) → (localWeilGroup F →ₜ* ℂˣ) := by
  letI := F.canonicalTopologicalData.topology
  exact fun η => η.comp (reciprocityUnits F e)

@[simp]
theorem weilCharacter_apply (e : ReciprocityCandidate F)
    (η : letI := F.canonicalTopologicalData.topology; F.Carrierˣ →ₜ* ℂˣ)
    (w : localWeilGroup F) :
    weilCharacter F e η w = η (reciprocityUnits F e w) := rfl

/-- Both constructions are the inverse directions of the published equivalence. -/
theorem weilCharacter_eq_symm (e : ReciprocityCandidate F) :
    weilCharacter F e =
      (weilCandidateCharacterEquiv F.canonicalTopologicalData
        (localResidueDegree F) e).symm := rfl

@[simp]
theorem fieldCharacter_weilCharacter (e : ReciprocityCandidate F)
    (η : letI := F.canonicalTopologicalData.topology; F.Carrierˣ →ₜ* ℂˣ) :
    fieldCharacter F e (weilCharacter F e η) = η :=
  (weilCandidateCharacterEquiv F.canonicalTopologicalData
    (localResidueDegree F) e).apply_symm_apply η

@[simp]
theorem weilCharacter_fieldCharacter (e : ReciprocityCandidate F)
    (χ : localWeilGroup F →ₜ* ℂˣ) :
    weilCharacter F e (fieldCharacter F e χ) = χ :=
  (weilCandidateCharacterEquiv F.canonicalTopologicalData
    (localResidueDegree F) e).symm_apply_apply χ

/-- The rank-one continuous Weil representation attached to a field character,
in the same carrier universe as the nonabelian exact virtual group. -/
def representation (e : ReciprocityCandidate F)
    (η : letI := F.canonicalTopologicalData.topology; F.Carrierˣ →ₜ* ℂˣ) :
    FiniteRepresentation.ContinuousObjects.{uF, uV} (localWeilGroup F) :=
  FiniteRepresentation.continuousCharacterLine (weilCharacter F e η)

@[simp]
theorem representation_rank (e : ReciprocityCandidate F)
    (η : letI := F.canonicalTopologicalData.topology; F.Carrierˣ →ₜ* ℂˣ) :
    (representation.{uF, uV} F e η).val.rank = 1 :=
  FiniteRepresentation.characterLine_rank _

/-- Its actual class in the exact-sequence Grothendieck group. -/
def virtualClass (e : ReciprocityCandidate F)
    (η : letI := F.canonicalTopologicalData.topology; F.Carrierˣ →ₜ* ℂˣ) :
    VirtualRepresentation.ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F) => A.IsContinuous) :=
  VirtualRepresentation.ExactGrothendieckGroup.characterClass (weilCharacter F e η)

@[simp]
theorem degree_virtualClass (e : ReciprocityCandidate F)
    (η : letI := F.canonicalTopologicalData.topology; F.Carrierˣ →ₜ* ℂˣ) :
    VirtualRepresentation.ExactGrothendieckGroup.degree
      (fun A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F) => A.IsContinuous)
      (virtualClass.{uF, uV} F e η) = 1 :=
  VirtualRepresentation.ExactGrothendieckGroup.degree_characterClass _

/-- Transporting an existing Weil character to the field and back preserves its
actual exact virtual class. -/
@[simp]
theorem virtualClass_fieldCharacter (e : ReciprocityCandidate F)
    (χ : localWeilGroup F →ₜ* ℂˣ) :
    virtualClass.{uF, uV} F e (fieldCharacter F e χ) =
      VirtualRepresentation.ExactGrothendieckGroup.characterClass.{uF, uV} χ := by
  unfold virtualClass
  rw [weilCharacter_fieldCharacter]

/-- Geometric order normalization uses the supplied reciprocity relation. -/
theorem reciprocityUnits_order (e : ReciprocityCandidate F)
    (he : LocalReciprocityCandidateRelation F.canonicalTopologicalData
      (localResidueDegree F) e) (w : localWeilGroup F) :
    F.canonicalTopologicalData.orderHom (reciprocityUnits F e w) = localDegree F w :=
  DFunLike.congr_fun he.1 (WeilQuotients.projection (localResidueDegree F) w)

/-- The chosen geometric Frobenius has order positive one under normalized reciprocity. -/
theorem reciprocityUnits_geometricFrobenius (e : ReciprocityCandidate F)
    (he : LocalReciprocityCandidateRelation F.canonicalTopologicalData
      (localResidueDegree F) e) :
    F.canonicalTopologicalData.ord
      (reciprocityUnits F e (localGeometricFrobenius F) : F.Carrier) = 1 := by
  have h := reciprocityUnits_order F e he (localGeometricFrobenius F)
  rw [localGeometricFrobenius_degree] at h
  exact congrArg Multiplicative.toAdd h

end Langlands.LocalFactor.RankOne
