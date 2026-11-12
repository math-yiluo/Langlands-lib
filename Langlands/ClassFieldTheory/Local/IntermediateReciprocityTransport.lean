import Langlands.Weil.Local.IntermediateWeil
import Langlands.LocalClassField.AbelianizationTransport
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityCompletionProof

/-!
# Reciprocity transport to prescribed intermediate fields
-/

noncomputable section

namespace Langlands.Weil.Local

open LocalClassField

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (E : FiniteIntermediateExtension F.Carrier)

local notation "EP" => E.asPadicField (p := p)

local instance : Algebra (Padic p) E.field := (EP).algebra

/-- The prescribed Galois map fixes precisely the actual intermediate field. -/
theorem intermediateGaloisMap_range :
    (intermediateGaloisMap F E).toMonoidHom.range = E.field.fixingSubgroup := by
  let c := intermediateClosureCorrection F E
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    apply (intermediateClosureCorrection_conj_mem F E _).mpr
    rw [← extensionGaloisMap_range F EP (intermediateEmbedding F E)]
    exact ⟨σ, rfl⟩
  · intro hτ
    have hc : c * (c⁻¹ * τ * c) * c⁻¹ = τ := by simp [mul_assoc]
    have hold : c⁻¹ * τ * c ∈
        (extensionIntermediateField F EP (intermediateEmbedding F E)).fixingSubgroup :=
      (intermediateClosureCorrection_conj_mem F E _).mp (hc.symm ▸ hτ)
    rw [← extensionGaloisMap_range F EP (intermediateEmbedding F E)] at hold
    obtain ⟨σ, hσ⟩ := hold
    refine ⟨σ, ?_⟩
    change c * extensionGaloisMap F EP (intermediateEmbedding F E) σ * c⁻¹ = τ
    change extensionGaloisMap F EP (intermediateEmbedding F E) σ = _ at hσ
    rw [hσ, hc]

/-- Conjugacy correction preserves injectivity of the absolute Galois map. -/
theorem intermediateGaloisMap_injective : Function.Injective (intermediateGaloisMap F E) := by
  intro σ τ h
  apply extensionGaloisMap_injective F EP (intermediateEmbedding F E)
  change intermediateClosureCorrection F E *
    extensionGaloisMap F EP (intermediateEmbedding F E) σ *
      (intermediateClosureCorrection F E)⁻¹ =
    intermediateClosureCorrection F E *
      extensionGaloisMap F EP (intermediateEmbedding F E) τ *
        (intermediateClosureCorrection F E)⁻¹ at h
  exact mul_left_cancel (mul_right_cancel h)

/-- The prescribed absolute Galois map is a closed embedding. -/
theorem intermediateGaloisMap_isClosedEmbedding :
    Topology.IsClosedEmbedding (intermediateGaloisMap F E) := by
  let : CharZero E.field :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) E.field).injective
  let : CompactSpace (Field.absoluteGaloisGroup E.field) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure E.field/E.field))
  let : T2Space (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure F.Carrier/F.Carrier))
  exact (intermediateGaloisMap F E).continuous.isClosedEmbedding
    (intermediateGaloisMap_injective F E)

/-- The standalone Galois group identifies with the prescribed fixing subgroup. -/
def intermediateGaloisEquiv :
    Field.absoluteGaloisGroup E.field ≃ₜ* E.field.fixingSubgroup := by
  let e : Field.absoluteGaloisGroup E.field ≃ₜ*
      (intermediateGaloisMap F E).toMonoidHom.range :=
    { toMulEquiv := MonoidHom.ofInjective (f := (intermediateGaloisMap F E).toMonoidHom)
        (intermediateGaloisMap_injective F E)
      continuous_toFun := (intermediateGaloisMap F E).continuous.subtype_mk _
      continuous_invFun := by
        rw [(intermediateGaloisMap_isClosedEmbedding F E).isEmbedding.continuous_iff]
        refine continuous_subtype_val.congr fun x => ?_
        exact (MonoidHom.apply_ofInjective_symm
          (f := (intermediateGaloisMap F E).toMonoidHom)
          (intermediateGaloisMap_injective F E) x).symm }
  exact e.trans
    { toMulEquiv := MulEquiv.subgroupCongr (intermediateGaloisMap_range F E)
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }

@[simp] theorem intermediateGaloisEquiv_apply (σ : Field.absoluteGaloisGroup E.field) :
    (intermediateGaloisEquiv F E σ).val =
      intermediateGaloisMap F E σ := rfl

/-- Weil projection commutes with the two prescribed-field comparisons. -/
theorem intermediateGaloisEquiv_projection (w : localWeilGroup EP) :
    intermediateGaloisEquiv F E (localProjection EP w) =
      E.weilGaloisProjection (localResidueDegree F) (intermediateWeilEquiv F E w) := by
  apply Subtype.ext
  rfl

end Langlands.Weil.Local

namespace Langlands.LocalClassField

open Weil.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (E : FiniteIntermediateExtension F.Carrier)

local notation "EP" => E.asPadicField (p := p)

/-- Comparison of the actual standalone and prescribed Weil abelianizations. -/
def intermediateWeilAbelianEquiv :
    WeilQuotients.Abelianization (localResidueDegree EP) ≃ₜ*
      TopologicalAbelianization
        (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :=
  abelianizationCongr (intermediateWeilEquiv F E)

/-- Comparison of the actual standalone and prescribed Galois abelianizations. -/
def intermediateGaloisAbelianEquiv :
    Field.absoluteGaloisGroupAbelianization E.field ≃ₜ*
      TopologicalAbelianization E.field.fixingSubgroup :=
  abelianizationCongr (intermediateGaloisEquiv F E)

@[simp] theorem intermediateWeilAbelianEquiv_projection (w : localWeilGroup EP) :
    intermediateWeilAbelianEquiv F E
      (WeilQuotients.projection (localResidueDegree EP) w) =
        abelianizationProjection _ (intermediateWeilEquiv F E w) := rfl

@[simp] theorem intermediateGaloisAbelianEquiv_projection
    (σ : Field.absoluteGaloisGroup E.field) :
    intermediateGaloisAbelianEquiv F E (absoluteAbelianizationProjection E.field σ) =
      abelianizationProjection _ (intermediateGaloisEquiv F E σ) := rfl

/-- The Weil-to-Galois projection square on closed-commutator quotients. -/
theorem intermediateAbelianEquiv_projection (w : WeilQuotients.Abelianization
    (localResidueDegree EP)) :
    intermediateGaloisAbelianEquiv F E
      (WeilQuotients.toGroupAbelianization (localResidueDegree EP) w) =
    E.weilGaloisAbelianProjection (localResidueDegree F)
      (intermediateWeilAbelianEquiv F E w) := by
  refine QuotientGroup.induction_on w ?_
  intro w
  change abelianizationProjection _ (intermediateGaloisEquiv F E (localProjection EP w)) =
    abelianizationProjection _
      (E.weilGaloisProjection (localResidueDegree F) (intermediateWeilEquiv F E w))
  rw [intermediateGaloisEquiv_projection]

end Langlands.LocalClassField

namespace Langlands.LocalClassField.CommonClosure

open Weil.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Transport a standalone candidate to the actual subgroup fixing the prescribed field. -/
def intermediateReciprocityCandidate (E : FiniteIntermediateExtension F.Carrier)
    (e : WeilReciprocityCandidate (canonicalData F E)
      (localResidueDegree (E.asPadicField (p := p)))) :
    letI := (canonicalData F E).topology
    TopologicalAbelianization
      (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) ≃ₜ* E.fieldˣ := by
  letI := (canonicalData F E).topology
  exact (intermediateWeilAbelianEquiv F E).symm.trans e

/-- Componentwise transport uses the same prescribed fields as the common-closure target. -/
def familyOfStandalone
    (e : ∀ E : FiniteIntermediateExtension F.Carrier,
      WeilReciprocityCandidate (canonicalData F E)
        (localResidueDegree (E.asPadicField (p := p)))) :
    CandidateFamily F (canonicalData F) (localResidueDegree F) :=
  fun E => intermediateReciprocityCandidate F E (e E)

/-- The transported map to Galois abelianization is the standalone map followed by
its actual prescribed-field comparison. -/
theorem galoisHom_familyOfStandalone
    (e : ∀ E : FiniteIntermediateExtension F.Carrier,
      WeilReciprocityCandidate (canonicalData F E)
        (localResidueDegree (E.asPadicField (p := p))))
    (E : FiniteIntermediateExtension F.Carrier) :
    letI := (canonicalData F E).topology
    galoisHom F (canonicalData F) (localResidueDegree F) (familyOfStandalone F e) E =
      (intermediateGaloisAbelianEquiv F E : _ →ₜ* _).comp
        (candidateGaloisHom (canonicalData F E)
          (localResidueDegree (E.asPadicField (p := p))) (e E)) := by
  let := (canonicalData F E).topology
  ext a
  change E.weilGaloisAbelianProjection (localResidueDegree F)
    (intermediateWeilAbelianEquiv F E ((e E).symm a)) =
      intermediateGaloisAbelianEquiv F E
        (WeilQuotients.toGroupAbelianization
          (localResidueDegree (E.asPadicField (p := p))) ((e E).symm a))
  exact (intermediateAbelianEquiv_projection F E _).symm

/-- Density transports through the constructed topological Galois equivalence. -/
theorem densityRelation_familyOfStandalone
    (e : ∀ E : FiniteIntermediateExtension F.Carrier,
      WeilReciprocityCandidate (canonicalData F E)
        (localResidueDegree (E.asPadicField (p := p))))
    (h : ∀ E : FiniteIntermediateExtension F.Carrier,
      GeometricWeilReciprocityRelation (E.asPadicField (p := p)) (canonicalData F E) (e E)) :
    DensityRelation F (canonicalData F) (localResidueDegree F) (familyOfStandalone F e) := by
  intro E
  let := (canonicalData F E).topology
  rw [galoisHom_familyOfStandalone]
  exact (intermediateGaloisAbelianEquiv F E).surjective.denseRange.comp
    (h E).2.1.1 (intermediateGaloisAbelianEquiv F E).continuous

/-- The published actual multiplicative-completion comparison transports to the
literal fixing subgroup, with the required diagram. -/
theorem completionRelation_familyOfStandalone
    (e : ∀ E : FiniteIntermediateExtension F.Carrier,
      WeilReciprocityCandidate (canonicalData F E)
        (localResidueDegree (E.asPadicField (p := p))))
    (h : ∀ E : FiniteIntermediateExtension F.Carrier,
      GeometricWeilReciprocityRelation (E.asPadicField (p := p)) (canonicalData F E) (e E)) :
    CompletionRelation F (canonicalData F) (localResidueDegree F) (familyOfStandalone F e) := by
  intro E
  let := (canonicalData F E).topology
  obtain ⟨c, hc, _⟩ := (profiniteReciprocityCompletion p (E.asPadicField (p := p))
    (canonicalData F E)
    (candidateGaloisHom (canonicalData F E)
      (localResidueDegree (E.asPadicField (p := p))) (e E)) (h E).2).2
  refine ⟨c.trans (intermediateGaloisAbelianEquiv F E), ?_⟩
  rw [galoisHom_familyOfStandalone]
  ext a
  change intermediateGaloisAbelianEquiv F E
    (c (LocalMultiplicative.completionMap (canonicalData F E) a)) =
      intermediateGaloisAbelianEquiv F E
        (candidateGaloisHom (canonicalData F E)
          (localResidueDegree (E.asPadicField (p := p))) (e E) a)
  rw [hc]

end Langlands.LocalClassField.CommonClosure
