import Langlands.Representation.Classification.RankOneUnlinkedEmbedding
import Langlands.Correspondence.RankOneExistence
import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Representation.Induction.BlockEquivalence

/-! Actual unlinked segment-product subrepresentations of inverse-ordered unramified series. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Unramified.OrderedSegmentEmbedding

open GeneralLinear Classification PadicField.TopologicalData Correspondence
open Classification.RankOneSegmentHom

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance glTopology (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance glGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- The actual rank-one cuspidal datum of the unramified character with value z. -/
def characterDatum (z : ℂˣ) : CuspidalDatum.{0, uF} F.canonicalTopologicalData :=
  rankOneDatum F F.canonicalTopologicalData
    (rankOneSupercuspidalObject.{uF, 0} F (character F z))

/-- On this actual character class, the scalar-uniformizer norm is the parameter norm. -/
theorem scalarUniformizerNorm_characterDatum (z : ℂˣ) :
    (characterDatum F z).scalarUniformizerNorm = ‖(z : ℂ)‖ := by
  let T := F.canonicalTopologicalData
  have hω : HasScalarCharacter
      (rankOneSupercuspidalObject.{uF, 0} F (character F z)).obj.representation
      GeneralLinear.scalar (character F z).toMonoidHom := by
    intro a v
    change ((character F z) (GeneralLinear.determinant (GeneralLinear.scalar a)) : ℂ) • v =
      ((character F z) a : ℂ) • v
    rw [GeneralLinear.determinant, Matrix.GeneralLinearGroup.det_scalar]
    simp
  have he := CuspidalDatum.scalarCharacter_eq_of_isRepresentedBy
    (characterDatum F z) (rankOneSupercuspidalObject.{uF, 0} F (character F z))
    rfl (character F z).toMonoidHom hω
  unfold CuspidalDatum.scalarUniformizerNorm
  rw [he]
  change ‖((character F z) T.uniformizerUnit : ℂ)‖ = _
  rw [character_uniformizer]

private theorem exists_of_singletons
    {n m : ℕ} (hm : 0 < m) (hN : n = m * 1)
    (C : BlockShape n) (hlen : C.length = m) (hsize : ∀ j, C.size j = 1)
    (X : Fin m → SupercuspidalRep.{uF, 0} (F := F.Carrier) (n := 1))
    (horder : Antitone (fun t => (rankOneDatum F F.canonicalTopologicalData (X t)).scalarUniformizerNorm)) :
    ∃ d : F.canonicalTopologicalData.SegmentProductDatum.{0, uF} n,
      d.HasSegmentSocles ∧ d.multisegment.IsUnlinked ∧
      (∀ j, (d.segments j).rank = 1) ∧
      d.multisegment.cuspidalContent =
        List.ofFn (fun t => rankOneDatum F F.canonicalTopologicalData (X t)) ∧
      IsIrreducibleSubrepresentation
        (F.canonicalTopologicalData.normalizedProductInduced C
          (fun j => ((hsize j).symm ▸ (X (Fin.cast hlen j)).obj :
            SmoothRep.{0, uF, 0} ℂ (GeneralLinear (C.size j) F.Carrier)).representation))
        d.induced.representation := by
  subst n
  have hC : C = BlockShape.uniform m 1 Nat.one_pos :=
    BlockShape.ext_of_size hlen (fun j => hsize j)
  subst C
  obtain ⟨d, hsoc, hu, hrank, hcontent, he⟩ :=
    RankOneUnlinkedEmbedding.exists_unlinked_embedding F F.canonicalTopologicalData hm X horder
  refine ⟨d, hsoc, hu, hrank, hcontent, he.of_equiv ?_⟩
  apply F.canonicalTopologicalData.normalizedProductInducedEquiv
  intro j
  apply SmoothRep.equivOfIso
  apply CategoryTheory.eqToIso
  apply eq_of_heq
  apply heq_of_eq
  congr 1

/-- A weakly norm-decreasing unramified principal series contains an irreducible
unlinked segment-socle product with exactly its unramified cuspidal content. -/
theorem exists_unlinked_segment_embedding
    (r : ℕ) (z : Fin (r + 1) → ℂˣ)
    (hz : Antitone (fun i => ‖(z i : ℂ)‖)) :
    ∃ d : F.canonicalTopologicalData.SegmentProductDatum.{0, uF} (r + 1),
      d.HasSegmentSocles ∧ d.multisegment.IsUnlinked ∧
      (∀ j, (d.segments j).rank = 1) ∧
      d.multisegment.cuspidalContent = List.ofFn (fun i => characterDatum F (z i)) ∧
      IsIrreducibleSubrepresentation (principalSeriesOfTuple F z) d.induced.representation := by
  let X := fun i => rankOneSupercuspidalObject.{uF, 0} F (character F (z i))
  have horder : Antitone (fun i => (rankOneDatum F F.canonicalTopologicalData (X i)).scalarUniformizerNorm) := by
    intro i j hij
    change (characterDatum F (z j)).scalarUniformizerNorm ≤
      (characterDatum F (z i)).scalarUniformizerNorm
    rw [scalarUniformizerNorm_characterDatum, scalarUniformizerNorm_characterDatum]
    exact hz hij
  obtain ⟨d, hsoc, hu, hrank, hcontent, he⟩ := exists_of_singletons F (Nat.succ_pos r)
    (Nat.mul_one (r + 1)).symm (borelShape r) rfl (fun _ => rfl) X horder
  have E : (F.canonicalTopologicalData.normalizedProductInduced (borelShape r)
      (fun i => (X i).obj.representation)).Equiv (principalSeriesOfTuple F z) :=
    F.canonicalTopologicalData.normalizedProductInducedEquiv (borelShape r)
      (fun i => FiniteRepresentation.characterLineEquiv.{uF, 0}
        (determinantQuasiCharacter F 1 (character F (z i))))
  exact ⟨d, hsoc, hu, hrank, hcontent, he.of_equiv E⟩

/-- A chosen actual unlinked product and its irreducible embedding for a weakly
norm-decreasing unramified tuple. -/
def unlinkedSegmentEmbeddingDatum
    (r : ℕ) (z : Fin (r + 1) → ℂˣ)
    (hz : Antitone (fun i => ‖(z i : ℂ)‖)) :
    { d : F.canonicalTopologicalData.SegmentProductDatum.{0, uF} (r + 1) //
      d.HasSegmentSocles ∧ d.multisegment.IsUnlinked ∧
      (∀ j, (d.segments j).rank = 1) ∧
      d.multisegment.cuspidalContent = List.ofFn (fun i => characterDatum F (z i)) ∧
      IsIrreducibleSubrepresentation (principalSeriesOfTuple F z) d.induced.representation } :=
  Classical.indefiniteDescription _ (exists_unlinked_segment_embedding F r z hz)

end Langlands.Unramified.OrderedSegmentEmbedding
