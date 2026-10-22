import Langlands.Weil.Local.ExtensionWeilRange
import Langlands.LocalClassField.AbelianizationTransport
import Langlands.ClassFieldTheory.Local.ExtensionFieldTransport

noncomputable section

namespace Langlands.LocalClassField

open Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The image subgroup is the actual pullback fixing subgroup of the chosen image field. -/
theorem extensionWeilRange_eq_fixing :
    extensionWeilRange F E f =
      pullbackFixingSubgroup F.Carrier (extensionFiniteIntermediate F E f).field (localResidueDegree F) := by
  rw [extensionWeilRange, extensionWeilMap_range, extensionGaloisMap_range]
  rfl

/-- Topological identification of the standalone Weil group with the common-closure subgroup. -/
def extensionImageWeilEquiv : localWeilGroup E ≃ₜ*
    pullbackFixingSubgroup F.Carrier (extensionFiniteIntermediate F E f).field (localResidueDegree F) :=
  (extensionWeilRangeEquiv F E f).trans
    { toMulEquiv := MulEquiv.subgroupCongr (extensionWeilRange_eq_fixing F E f)
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }

@[simp] theorem extensionImageWeilEquiv_apply (w : localWeilGroup E) :
    (extensionImageWeilEquiv F E f w : localWeilGroup F) = extensionWeilMap F E f w := rfl

/-- Transport on the actual closed-commutator quotients. -/
def extensionImageAbelianEquiv :
    WeilQuotients.Abelianization (localResidueDegree E) ≃ₜ*
      TopologicalAbelianization
        (pullbackFixingSubgroup F.Carrier (extensionFiniteIntermediate F E f).field (localResidueDegree F)) :=
  abelianizationCongr (extensionImageWeilEquiv F E f)

@[simp] theorem extensionImageAbelianEquiv_projection (w : localWeilGroup E) :
    extensionImageAbelianEquiv F E f (WeilQuotients.projection (localResidueDegree E) w) =
      abelianizationProjection _ (extensionImageWeilEquiv F E f w) := rfl

/-- Base-field degree on the common-closure quotient is residue degree times standalone degree. -/
theorem extensionImageAbelianEquiv_degree
    (w : WeilQuotients.Abelianization (localResidueDegree E)) :
    (extensionFiniteIntermediate F E f).weilDegree (localResidueDegree F)
        (extensionImageAbelianEquiv F E f w) =
      WeilQuotients.degree (localResidueDegree E) w ^ extensionResidueDegree F E f := by
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  refine QuotientGroup.induction_on w ?_
  intro w
  exact localDegree_extensionWeilMap F E f w

/-- The actual inclusion multiplies geometric integer degree by the relative residue degree. -/
theorem extensionImageWeilEquiv_degree (w : localWeilGroup E) :
    localDegreeInt F (extensionImageWeilEquiv F E f w : localWeilGroup F) =
      extensionResidueDegree F E f * localDegreeInt E w :=
  localDegreeInt_extensionWeilMap F E f w

/-- The actual inclusion preserves the normalized Weil norm character. -/
theorem extensionImageWeilEquiv_normCharacter (w : localWeilGroup E) :
    localNormCharacter F (extensionImageWeilEquiv F E f w : localWeilGroup F) =
      localNormCharacter E w :=
  localNormCharacter_extensionWeilMap F E f w

local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology

local instance : TopologicalSpace (extensionFiniteIntermediate F E f).field :=
  (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology

variable (e : CommonClosure.CandidateFamily F (CommonClosure.canonicalData F)
  (localResidueDegree F))

/-- Transport the supplied family component along the actual quotient and unit equivalences. -/
def extensionReciprocityCandidate :
    WeilReciprocityCandidate E.canonicalTopologicalData (localResidueDegree E) := by
  letI := E.canonicalTopologicalData.topology
  letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
  exact ((extensionImageAbelianEquiv F E f).trans
    (e (extensionFiniteIntermediate F E f))).trans (extensionIntermediateUnitsEquiv F E f).symm

/-- On quotient generators the construction uses exactly the supplied image-field component. -/
@[simp] theorem extensionReciprocityCandidate_projection (w : localWeilGroup E) :
    extensionReciprocityCandidate F E f e (WeilQuotients.projection (localResidueDegree E) w) =
      (extensionIntermediateUnitsEquiv F E f).symm
        (e (extensionFiniteIntermediate F E f)
          (abelianizationProjection _ (extensionImageWeilEquiv F E f w))) := rfl

/-- Descent and the two actual comparisons commute with character transport. -/
theorem extensionReciprocityCandidate_character
    (χ : pullbackFixingSubgroup F.Carrier (extensionFiniteIntermediate F E f).field
      (localResidueDegree F) →ₜ* ℂˣ) (a : E.Carrierˣ) :
    weilCandidateCharacterEquiv E.canonicalTopologicalData (localResidueDegree E)
      (extensionReciprocityCandidate F E f e)
      (χ.comp (extensionImageWeilEquiv F E f : localWeilGroup E →ₜ* _)) a =
        characterTransport (e (extensionFiniteIntermediate F E f))
          (abelianizationLift χ) (extensionIntermediateUnitsEquiv F E f a) := by
  change abelianizationLift (χ.comp (extensionImageWeilEquiv F E f : localWeilGroup E →ₜ* _))
    ((extensionReciprocityCandidate F E f e).symm a) = _
  rw [abelianizationLift_comp_equiv]
  change abelianizationLift χ
    (extensionImageAbelianEquiv F E f ((extensionImageAbelianEquiv F E f).symm
      ((e (extensionFiniteIntermediate F E f)).symm
        (extensionIntermediateUnitsEquiv F E f a)))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- Character evaluation on the constructed image of a Weil generator recovers that generator. -/
theorem extensionReciprocityCandidate_character_projection
    (χ : localWeilGroup E →ₜ* ℂˣ) (w : localWeilGroup E) :
    weilCandidateCharacterEquiv E.canonicalTopologicalData (localResidueDegree E)
      (extensionReciprocityCandidate F E f e) χ
      (extensionReciprocityCandidate F E f e (WeilQuotients.projection (localResidueDegree E) w)) =
        χ w := by
  change abelianizationLift χ ((extensionReciprocityCandidate F E f e).symm
    (extensionReciprocityCandidate F E f e (WeilQuotients.projection (localResidueDegree E) w))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

variable (hn : CommonClosure.NormalizationRelation F (CommonClosure.canonicalData F)
  (localResidueDegree F) F.canonicalTopologicalData e)

include hn

/-- Common-closure normalization becomes the standalone normalized absolute-value formula. -/
theorem extensionReciprocityCandidate_normalizedAbs
    (w : WeilQuotients.Abelianization (localResidueDegree E)) :
    E.canonicalTopologicalData.normalizedAbs (extensionReciprocityCandidate F E f e w : E.Carrier) =
      (E.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-Multiplicative.toAdd (WeilQuotients.degree (localResidueDegree E) w)) := by
  change E.canonicalTopologicalData.normalizedAbs
    ((extensionIntermediateUnitsEquiv F E f).symm
      (e (extensionFiniteIntermediate F E f) (extensionImageAbelianEquiv F E f w)) : E.Carrier) = _
  rw [extensionIntermediateUnitsEquiv_symm_normalizedAbs]
  rw [hn, extensionImageAbelianEquiv_degree, extensionResidueCardinality F E f,
    Nat.cast_pow, toAdd_pow, nsmul_eq_mul, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/-- The transported candidate has the plus-sign geometric order normalization. -/
theorem extensionReciprocityCandidate_geometricOrder :
    GeometricOrderRelation E.canonicalTopologicalData (localResidueDegree E)
      (extensionReciprocityCandidate F E f e) := by
  apply MonoidHom.ext
  intro w
  change Multiplicative.ofAdd (E.canonicalTopologicalData.ord
    (extensionReciprocityCandidate F E f e w : E.Carrier)) =
      WeilQuotients.degree (localResidueDegree E) w
  apply Multiplicative.toAdd.injective
  change E.canonicalTopologicalData.ord (extensionReciprocityCandidate F E f e w : E.Carrier) = _
  have h := extensionReciprocityCandidate_normalizedAbs F E f e hn w
  rw [E.canonicalTopologicalData.normalizedAbs_of_ne_zero
    (extensionReciprocityCandidate F E f e w).ne_zero] at h
  have hq : (1 : ℝ) < E.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast E.canonicalTopologicalData.residueCardinality_gt_one
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq) h)

/-- The actual standalone norm character transports to the normalized absolute value. -/
theorem extensionReciprocityCandidate_normCharacter (a : E.Carrierˣ) :
    (weilCandidateCharacterEquiv E.canonicalTopologicalData (localResidueDegree E)
      (extensionReciprocityCandidate F E f e) (localNormCharacter E) a : ℂ) =
        (E.canonicalTopologicalData.normalizedAbs (a : E.Carrier) : ℂ) := by
  obtain ⟨w, rfl⟩ := (extensionReciprocityCandidate F E f e).surjective a
  refine QuotientGroup.induction_on w ?_
  intro w
  change (weilCandidateCharacterEquiv E.canonicalTopologicalData (localResidueDegree E)
    (extensionReciprocityCandidate F E f e) (localNormCharacter E)
      (extensionReciprocityCandidate F E f e
        (WeilQuotients.projection (localResidueDegree E) w)) : ℂ) = _
  rw [extensionReciprocityCandidate_character_projection F E f e (localNormCharacter E) w,
    extensionReciprocityCandidate_normalizedAbs F E f e hn]
  change (residueNormCharacter E.canonicalTopologicalData (localDegree E) w : ℂ) = _
  rw [residueNormCharacter_apply]
  push_cast
  rfl

end Langlands.LocalClassField
