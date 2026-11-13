import Langlands.LocalFactor.CommonClosure
import Langlands.ClassFieldTheory.Local.ReciprocityTransport
import Langlands.LocalFactor.RankOne

/-! # Reciprocity on a conjugate of the image of a standalone extension -/

noncomputable section

set_option autoImplicit false

universe uF uE

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure LocalClassField Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Standalone p-adic fields carry their canonical topology in this file. -/
local instance conjugateTransportTopology (E : PadicField.{uE} p) : TopologicalSpace E.Carrier :=
  E.canonicalTopologicalData.topology

/-- Reciprocity components for two finite intermediate fields with the same underlying field
agree on equal Weil elements. -/
theorem reciprocityUnits_coe_eq_of_field_eq (e : ReciprocityFamily F) (A B : Extension F)
    (h : A.field = B.field) (x : weilSubgroup F A) (y : weilSubgroup F B)
    (hxy : (x : localWeilGroup F) = (y : localWeilGroup F)) :
    ((reciprocityUnits F e A x : A.field) : AlgebraicClosure F.Carrier) =
      ((reciprocityUnits F e B y : B.field) : AlgebraicClosure F.Carrier) := by
  have hAB : A = B := Subtype.ext h
  subst B
  have hxy' : x = y := Subtype.ext hxy
  subst y
  rfl

/-- The conjugation square of a normalized family, read in the common closure: the component
for `σ(M)` at `w x w⁻¹` is `σ` of the component for `M` at `x`, where `σ` is the Galois
projection of `w`. -/
theorem reciprocityUnits_weilConjugation (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (M : Extension F) (w : localWeilGroup F)
    (x : weilSubgroup F M) :
    ((reciprocityUnits F e (M.conj (localProjection F w))
        (M.weilConjugation (localResidueDegree F) w x) : (M.conj (localProjection F w)).field) :
        AlgebraicClosure F.Carrier) =
      AlgEquiv.toAlgHom (localProjection F w)
        ((reciprocityUnits F e M x : M.field) : AlgebraicClosure F.Carrier) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have hc := DFunLike.congr_fun (he.1.2.2.1 w M) (abelianizationProjection _ x)
  have hc' : reciprocityUnits F e (M.conj (localProjection F w))
      (M.weilConjugation (localResidueDegree F) w x) =
      M.unitsConjugation (localProjection F w) (reciprocityUnits F e M x) := hc
  rw [hc']
  rfl

/-- The reciprocity map of a candidate is onto the units. -/
theorem rankOne_reciprocityUnits_surjective {E : PadicField.{uE} p}
    (e : RankOne.ReciprocityCandidate E) :
    Function.Surjective (RankOne.reciprocityUnits E e) := by
  intro a
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (e.symm a)
  refine ⟨w, ?_⟩
  change e (QuotientGroup.mk w) = a
  rw [hw]
  exact e.apply_symm_apply a

section Extension

variable (E : PadicField.{uE} p) (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- On the image of `W_E`, the component of the family for the image field of `E` is the
transported candidate, read through the chosen embedding `E → \bar F`. -/
theorem reciprocityUnits_extensionImage (e : ReciprocityFamily F) (y : localWeilGroup E) :
    ((reciprocityUnits F e (extensionFiniteIntermediate F E f)
        (extensionImageWeilEquiv F E f y) : (extensionFiniteIntermediate F E f).field) :
        AlgebraicClosure F.Carrier) =
      extensionFieldEmbedding F E f
        (RankOne.reciprocityUnits E (extensionReciprocityCandidate F E f e) y :
          E.Carrier) := by
  let := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
  have h : RankOne.reciprocityUnits E (extensionReciprocityCandidate F E f e) y =
      (extensionIntermediateUnitsEquiv F E f).symm
        (reciprocityUnits F e (extensionFiniteIntermediate F E f)
          (extensionImageWeilEquiv F E f y)) := rfl
  rw [h, ← extensionIntermediatePadicEquiv_coe]
  have h2 : (extensionIntermediatePadicEquiv F E f
      (((extensionIntermediateUnitsEquiv F E f).symm
        (reciprocityUnits F e (extensionFiniteIntermediate F E f)
          (extensionImageWeilEquiv F E f y)) : E.Carrierˣ) : E.Carrier)) =
      (reciprocityUnits F e (extensionFiniteIntermediate F E f)
        (extensionImageWeilEquiv F E f y) : (extensionFiniteIntermediate F E f).field) :=
    congrArg Units.val ((extensionIntermediateUnitsEquiv F E f).apply_symm_apply _)
  rw [h2]

variable {E f}

/-- If `w` carries the chosen embedding `E → \bar F` onto an embedding `b` with image `L`,
then conjugation by `w` carries the image field of `E` onto `L`. -/
theorem conj_extensionFiniteIntermediate_field (L : Extension F)
    (b : E.Carrier → AlgebraicClosure F.Carrier)
    (hb : ∀ z, z ∈ L.field ↔ ∃ x, b x = z) (w : localWeilGroup F)
    (hw : ∀ x, AlgEquiv.toAlgHom (localProjection F w) (extensionFieldEmbedding F E f x) = b x) :
    ((extensionFiniteIntermediate F E f).conj (localProjection F w)).field = L.field := by
  let := extensionAlgebra F E f
  ext z
  rw [hb z]
  change z ∈ (extensionIntermediateField F E f).map
      (AlgEquiv.toAlgHom (localProjection F w)) ↔ _
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (AlgHom.mem_fieldRange (f := extensionFieldAlgHom F E f)).mp hy
    exact ⟨x, (hw x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨extensionFieldEmbedding F E f x,
      (AlgHom.mem_fieldRange (f := extensionFieldAlgHom F E f)).mpr ⟨x, rfl⟩, hw x⟩

/-- Under the same hypothesis, `w (image of y) w⁻¹` lies in the Weil subgroup of `L`. -/
theorem conj_extensionWeilMap_mem (L : Extension F) (w : localWeilGroup F)
    (hL : ((extensionFiniteIntermediate F E f).conj (localProjection F w)).field = L.field)
    (y : localWeilGroup E) :
    w * extensionWeilMap F E f y * w⁻¹ ∈ weilSubgroup F L := by
  have h := (extensionFiniteIntermediate F E f).conj_mem_pullbackFixingSubgroup
    (localResidueDegree F) w (extensionImageWeilEquiv F E f y).2
  change w * extensionWeilMap F E f y * w⁻¹ ∈ pullbackFixingSubgroup F.Carrier
    ((extensionFiniteIntermediate F E f).conj (localProjection F w)).field
    (localResidueDegree F) at h
  rw [hL] at h
  exact h

/-- **Reciprocity on a conjugate image field.** Let `e` be normalized and `w` a Weil element
carrying the chosen embedding `E → \bar F` onto an embedding `b` with image `L`. Then the
component of `e` for `L` at `w y w⁻¹`, for `y ∈ W_E`, is `b` of the transported candidate of
`E` at `y`. -/
theorem reciprocityUnits_conj_extension (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (L : Extension F) (b : E.Carrier → AlgebraicClosure F.Carrier)
    (w : localWeilGroup F)
    (hw : ∀ x, AlgEquiv.toAlgHom (localProjection F w) (extensionFieldEmbedding F E f x) = b x)
    (hL : ((extensionFiniteIntermediate F E f).conj (localProjection F w)).field = L.field)
    (y : localWeilGroup E) :
    ((reciprocityUnits F e L ⟨w * extensionWeilMap F E f y * w⁻¹,
        conj_extensionWeilMap_mem F L w hL y⟩ : L.field) : AlgebraicClosure F.Carrier) =
      b (RankOne.reciprocityUnits E (extensionReciprocityCandidate F E f e) y : E.Carrier) := by
  rw [← reciprocityUnits_coe_eq_of_field_eq F e _ L hL
    ((extensionFiniteIntermediate F E f).weilConjugation (localResidueDegree F) w
      (extensionImageWeilEquiv F E f y)) _ rfl,
    reciprocityUnits_weilConjugation F e he, reciprocityUnits_extensionImage, hw]

end Extension

end Langlands.LocalFactor.NonabelianBrauer
