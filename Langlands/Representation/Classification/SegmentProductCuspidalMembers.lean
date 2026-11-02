import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof

/-! # The ordered cuspidal members of a segment product -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.SegmentProductCuspidalEmbedding

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ## The members of a segment product -/

theorem ofFn_multiset_eq_sum {α : Type*} {k : ℕ} (f : Fin k → α) :
    (List.ofFn f : Multiset α) = ∑ i, ({f i} : Multiset α) := by
  simpa only [Multiset.map_coe, List.map_ofFn, Multiset.sum_coe, List.sum_ofFn,
    Function.comp_apply] using (Multiset.sum_map_singleton (List.ofFn f : Multiset α)).symm

variable {T}

/-- Each segment block is refined into its members. -/
def memberRefinement {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    BlockRefinement d.shape :=
  fun j => BlockShape.uniform (d.segments j).length (d.segments j).rank
    (d.segments j).rank_pos

/-- All members of all segments, in order. -/
def memberFamily {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    Fin (d.shape.flatten (memberRefinement d)).length → CuspidalDatum.{uV, uF} T :=
  fun k =>
    let q := (d.shape.flattenBlockEquiv (memberRefinement d)).symm k
    (d.segments q.1).member q.2.val

theorem memberFamily_sum {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    ∑ k, (memberFamily d k).rank = n :=
  (d.shape.flatten (memberRefinement d)).sum_eq

/-- Twists of supplied representatives of the bases. -/
def memberRepresentatives {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (A : letI := T.topology
      ∀ j, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (d.segments j).rank)) :
    letI := T.topology
    ∀ k, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (memberFamily d k).rank) :=
  letI := T.topology
  fun k =>
    let q := (d.shape.flattenBlockEquiv (memberRefinement d)).symm k
    SupercuspidalRep.twist
      (T.determinantPowerCharacter (d.segments q.1).rank (q.2.val : ℝ))
      (T.isOpen_ker_determinantPowerCharacter _ _)
      (T.ker_determinant_le_ker_determinantPowerCharacter _ _) (A q.1)

theorem memberRepresentatives_represent {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (A : letI := T.topology
      ∀ j, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (d.segments j).rank))
    (hA : ∀ j, (d.segments j).base.IsRepresentedBy (A j)) :
    ∀ k, (memberFamily d k).IsRepresentedBy (memberRepresentatives d A k) := by
  let := T.topology
  intro k
  let q := (d.shape.flattenBlockEquiv (memberRefinement d)).symm k
  change T.supercuspidalClassRealPowerTwist (d.segments q.1).rank (q.2.val : ℝ)
      (A q.1).isoClass =
    T.supercuspidalClassRealPowerTwist (d.segments q.1).rank (q.2.val : ℝ)
      (d.segments q.1).base.cls
  exact congrArg (T.supercuspidalClassRealPowerTwist _ _) (hA q.1)

variable (T) in
private def memberRankIso {ι : Type} (r : ι → ℕ)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (r i) F.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ σ i) ≅ σ j := by
  subst j
  exact Iso.refl _

/-- The supercuspidal product of all members is the product of the segment
inductions. -/
theorem memberInducedIso {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (A : letI := T.topology
      ∀ j, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (d.segments j).rank)) :
    letI := T.topology
    Nonempty (T.cuspidalProductInduced (memberFamily d) (memberFamily_sum d)
      (memberRepresentatives d A) ≅
      (T.normalizedProductInductionFunctor d.shape).obj
        (fun j => T.segmentInduced (A j).obj (d.segments j).length
          (d.segments j).rank_pos)) := by
  let := T.topology
  let S := memberRefinement d
  let B := d.shape.flatten S
  let e := d.shape.flattenBlockEquiv S
  let σ : ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size k) F.Carrier) :=
    fun k => (memberRepresentatives d A k).obj
  let h (q : (j : Fin d.shape.length) × Fin (S j).length) :
      (S q.1).size q.2 = B.size (e q) :=
    (d.shape.flatten_size_flattenBlockEquiv S q).symm
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF, uV} F T
    n B d.shape S e h (fun j k x => d.shape.index_index_eq_flatten S ⟨j, k⟩ x) σ
  have einner (j : Fin d.shape.length) :
      (T.normalizedProductInductionFunctor (S j)).obj
        (fun k => (h ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩)) ≅
      T.segmentInduced (A j).obj (d.segments j).length (d.segments j).rank_pos := by
    apply (T.normalizedProductInductionFunctor (S j)).mapIso
    apply Pi.isoMk
    intro k
    exact memberRankIso T
      (fun q : (j : Fin d.shape.length) × Fin (S j).length => (S q.1).size q.2)
      (fun q => T.segmentFactor (A q.1).obj (q.2.val : ℝ))
      (e.symm_apply_apply ⟨j, k⟩)
  exact ⟨ereg ≪≫ (T.normalizedProductInductionFunctor d.shape).mapIso (Pi.isoMk einner)⟩

theorem memberFamily_content {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    (List.ofFn (memberFamily d) : Multiset _) = d.multisegment.cuspidalContent := by
  let S := memberRefinement d
  let e := d.shape.flattenBlockEquiv S
  calc
    (List.ofFn (memberFamily d) : Multiset _) =
        ∑ k, ({memberFamily d k} : Multiset _) := ofFn_multiset_eq_sum _
    _ = ∑ q : (j : Fin d.shape.length) × Fin (S j).length,
        ({(d.segments q.1).member q.2.val} : Multiset _) :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    _ = ∑ j, ∑ k : Fin (S j).length,
        ({(d.segments j).member k.val} : Multiset _) :=
      Fintype.sum_sigma' (fun j (k : Fin (S j).length) =>
        ({(d.segments j).member k.val} : Multiset _))
    _ = ∑ j, (d.segments j).cuspidalContent :=
      Finset.sum_congr rfl (fun j _ => (ofFn_multiset_eq_sum _).symm)
    _ = d.multisegment.cuspidalContent := by
      simp only [SegmentProductDatum.multisegment, Multisegment.cuspidalContent,
        Multiset.map_coe, List.map_ofFn, Multiset.sum_coe, List.sum_ofFn, Function.comp_apply]

end Langlands.Classification.SegmentProductCuspidalEmbedding
