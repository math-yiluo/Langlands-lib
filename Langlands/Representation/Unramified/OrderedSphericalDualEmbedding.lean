import Langlands.Representation.Unramified.OrderedSegmentEmbedding
import Langlands.Representation.Unramified.PrincipalSeriesDuality
import Langlands.Representation.Unramified.SphericalSegmentProduct
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! Spherical irreducible subobjects of smooth duals of ordered unramified series. -/

noncomputable section

namespace Langlands.Unramified

open Correspondence Classification

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance quotientFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance quotientGLTopology (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance quotientGLGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

private theorem inverseTuple_norm_antitone {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    Antitone (fun i => ‖(((z i)⁻¹ : ℂˣ) : ℂ)‖) := by
  intro i j hij
  change ‖(((z j)⁻¹ : ℂˣ) : ℂ)‖ ≤ ‖(((z i)⁻¹ : ℂˣ) : ℂ)‖
  simp only [Units.val_inv_eq_inv_val, norm_inv]
  exact inv_anti₀ (norm_pos_iff.mpr (Units.ne_zero (z i))) (hz hij)

private theorem characterObject_scalar (a : ℂˣ) :
    HasScalarCharacter
      (rankOneSupercuspidalObject.{uF, 0} F (character F a)).obj.representation
      (MonoidHom.id _) ((character F a).toMonoidHom.comp GeneralLinear.determinant) := by
  intro g v
  rfl

/-- The inverse tuple gives an actual irreducible segment-product subobject of
the smooth dual, with the exact inverse-character cuspidal content. -/
theorem exists_inverse_tuple_segment_dual_embedding
    {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    ∃ d : F.canonicalTopologicalData.SegmentProductDatum.{0, uF} (r + 1),
      d.HasSegmentSocles ∧ d.multisegment.IsUnlinked ∧
      (∀ j, (d.segments j).rank = 1) ∧
      d.multisegment.cuspidalContent = List.ofFn
        (fun i => OrderedSegmentEmbedding.characterDatum F ((z i)⁻¹)) ∧
      IsIrreducibleSubrepresentation (smoothContragredient (principalSeriesOfTuple F z))
        d.induced.representation := by
  obtain ⟨d, hsoc, hu, hr, hc, he⟩ := OrderedSegmentEmbedding.exists_unlinked_segment_embedding
    F r (fun i => (z i)⁻¹) (inverseTuple_norm_antitone z hz)
  exact ⟨d, hsoc, hu, hr, hc, he.of_equiv (principalSeriesOfTupleSmoothDualEquiv F z).symm⟩

/-- For a Langlands-ordered tuple the smooth dual contains an actual
irreducible admissible spherical segment-product representation. -/
theorem exists_spherical_irreducible_subrepresentation_smoothDual
    {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    ∃ B : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (r + 1) F.Carrier),
      IsAdmissible B.representation ∧
      IsIrreducibleSubrepresentation (smoothContragredient (principalSeriesOfTuple F z))
        B.representation ∧
      fixedVectors B.representation (sphericalSubgroup F r) ≠ ⊥ := by
  obtain ⟨d, hsoc, _, _, hc, he⟩ := exists_inverse_tuple_segment_dual_embedding F z hz
  have hfixed : fixedVectors d.induced.representation (sphericalSubgroup F r) ≠ ⊥ :=
    SphericalProduct.segmentProduct_fixedVectors_ne_bot F d hsoc
      (fun i => rankOneSupercuspidalObject.{uF, 0} F (character F ((z i)⁻¹)))
      (fun i => ⟨(character F ((z i)⁻¹)).toMonoidHom,
        character_isUnramified F ((z i)⁻¹), characterObject_scalar F ((z i)⁻¹)⟩) hc
  obtain ⟨_, j, hj⟩ := he.of_equiv (principalSeriesOfTupleSmoothDualEquiv F z)
  have hadm : IsAdmissible d.induced.representation :=
    isAdmissible_of_injective j hj
      (SphericalExistence.principalSeriesOfTuple_isAdmissible F (fun i => (z i)⁻¹))
  exact ⟨d.induced, hadm, he, hfixed⟩

/-- A chosen actual irreducible admissible spherical representation and its
embedding into the smooth dual of a Langlands-ordered unramified series. -/
def sphericalDualEmbeddingDatum
    {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    { B : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (r + 1) F.Carrier) //
      IsAdmissible B.representation ∧
      IsIrreducibleSubrepresentation (smoothContragredient (principalSeriesOfTuple F z))
        B.representation ∧
      fixedVectors B.representation (sphericalSubgroup F r) ≠ ⊥ } :=
  Classical.indefiniteDescription _
    (exists_spherical_irreducible_subrepresentation_smoothDual F z hz)

end Langlands.Unramified
