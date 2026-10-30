import Langlands.Representation.Parabolic.InducedMapSurjectivity
import Langlands.Representation.Classification.SegmentHeadProductCuspidalSupportStatement
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Tensor.ExternalMapSurjectivityProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem ofFn_multiset_eq_sum {α : Type*} {k : ℕ} (f : Fin k → α) :
    (List.ofFn f : Multiset α) = ∑ i, ({f i} : Multiset α) := by
  simpa only [Multiset.map_coe, List.map_ofFn, Multiset.sum_coe, List.sum_ofFn, Function.comp_apply]
    using (Multiset.sum_map_singleton (List.ofFn f : Multiset α)).symm

private def memberRefinement {n : ℕ} (d : T.SegmentProductDatum.{max uF uV,uF} n) :
    BlockRefinement d.shape :=
  fun j => BlockShape.uniform (d.segments j).length (d.segments j).rank
    (d.segments j).rank_pos

private def memberFamily {n : ℕ} (d : T.SegmentProductDatum.{max uF uV,uF} n) :
    Fin (d.shape.flatten (memberRefinement F T d)).length →
      CuspidalDatum.{max uF uV,uF} T :=
  fun k =>
    let q := (d.shape.flattenBlockEquiv (memberRefinement F T d)).symm k
    (d.segments q.1).member q.2.val

private theorem memberFamily_sum {n : ℕ} (d : T.SegmentProductDatum.{max uF uV,uF} n) :
    ∑ k, (memberFamily F T d k).rank = n :=
  (d.shape.flatten (memberRefinement F T d)).sum_eq

private def memberRepresentatives {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV,uF} n)
    (A : letI := T.topology
      ∀ j, SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := (d.segments j).rank)) :
    letI := T.topology
    ∀ k, SupercuspidalRep.{uF,max uF uV}
      (F := F.Carrier) (n := (memberFamily F T d k).rank) :=
  letI := T.topology
  fun k =>
    let q := (d.shape.flattenBlockEquiv (memberRefinement F T d)).symm k
    SupercuspidalRep.twist
      (T.determinantPowerCharacter (d.segments q.1).rank (q.2.val : ℝ))
      (T.isOpen_ker_determinantPowerCharacter _ _)
      (T.ker_determinant_le_ker_determinantPowerCharacter _ _) (A q.1)

private theorem memberRepresentatives_represent {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV,uF} n)
    (A : letI := T.topology
      ∀ j, SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := (d.segments j).rank))
    (hA : ∀ j, (d.segments j).base.IsRepresentedBy (A j)) :
    ∀ k, (memberFamily F T d k).IsRepresentedBy (memberRepresentatives F T d A k) := by
  let := T.topology
  intro k
  let q := (d.shape.flattenBlockEquiv (memberRefinement F T d)).symm k
  change T.supercuspidalClassRealPowerTwist (d.segments q.1).rank (q.2.val : ℝ)
      (A q.1).isoClass =
    T.supercuspidalClassRealPowerTwist (d.segments q.1).rank (q.2.val : ℝ)
      (d.segments q.1).base.cls
  exact congrArg (T.supercuspidalClassRealPowerTwist _ _) (hA q.1)

private def memberRankIso {ι : Type} (r : ι → ℕ)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (r i) F.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ σ i) ≅ σ j := by
  subst j
  exact Iso.refl _

private theorem memberInducedIso {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV,uF} n)
    (A : letI := T.topology
      ∀ j, SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := (d.segments j).rank)) :
    letI := T.topology
    Nonempty (T.cuspidalProductInduced (memberFamily F T d) (memberFamily_sum F T d)
      (memberRepresentatives F T d A) ≅
      (T.normalizedProductInductionFunctor d.shape).obj
        (fun j => T.segmentInduced (A j).obj (d.segments j).length
          (d.segments j).rank_pos)) := by
  let := T.topology
  let S := memberRefinement F T d
  let B := d.shape.flatten S
  let e := d.shape.flattenBlockEquiv S
  let σ : ∀ k, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size k) F.Carrier) :=
    fun k => (memberRepresentatives F T d A k).obj
  let h (q : (j : Fin d.shape.length) × Fin (S j).length) :
      (S q.1).size q.2 = B.size (e q) :=
    (d.shape.flatten_size_flattenBlockEquiv S q).symm
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF,max uF uV} F T
    n B d.shape S e h (fun j k x => d.shape.index_index_eq_flatten S ⟨j,k⟩ x) σ
  have einner (j : Fin d.shape.length) :
      (T.normalizedProductInductionFunctor (S j)).obj
        (fun k => (h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩)) ≅
      T.segmentInduced (A j).obj (d.segments j).length (d.segments j).rank_pos := by
    apply (T.normalizedProductInductionFunctor (S j)).mapIso
    apply Pi.isoMk
    intro k
    exact memberRankIso F T
      (fun q : (j : Fin d.shape.length) × Fin (S j).length => (S q.1).size q.2)
      (fun q => T.segmentFactor (A q.1).obj (q.2.val : ℝ))
      (e.symm_apply_apply ⟨j,k⟩)
  exact ⟨ereg ≪≫ (T.normalizedProductInductionFunctor d.shape).mapIso (Pi.isoMk einner)⟩

private theorem memberFamily_content {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV,uF} n) :
    (List.ofFn (memberFamily F T d) : Multiset _) = d.multisegment.cuspidalContent := by
  let S := memberRefinement F T d
  let e := d.shape.flattenBlockEquiv S
  calc
    (List.ofFn (memberFamily F T d) : Multiset _) =
        ∑ k, ({memberFamily F T d k} : Multiset _) := ofFn_multiset_eq_sum _
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

/-- The actual product of supplied segment heads has their exact cuspidal
member multiset as a supercuspidal support whenever that product is irreducible. -/
theorem segmentHeadProductCuspidalSupport :
    SegmentHeadProductCuspidalSupport.{uF,uV} F T := by
  classical
  let := T.topology
  intro n d hd hirr
  have hq (j : Fin d.length) := (hd j).isSegmentQuotient
  choose A hA hquot using hq
  choose hblock q hsurj using hquot
  let source := fun j => T.segmentInduced (A j).obj (d.segments j).length
    (d.segments j).rank_pos
  let Q : (T.normalizedProductInductionFunctor d.shape).obj source ⟶ d.induced :=
    SmoothRep.ofHom (T.normalizedProductInducedMap d.shape q)
  have hQ : Function.Surjective (SmoothRep.hom Q) :=
    normalizedProductMap_surjective F T d.shape source d.blocks q hsurj
  obtain ⟨e⟩ := memberInducedIso F T d A
  refine ⟨_, memberFamily F T d, memberFamily_content F T d, memberFamily_sum F T d,
    memberRepresentatives F T d A, memberRepresentatives_represent F T d A hA,
    hirr, ?_⟩
  apply SmoothRep.IsQuotient.isSubquotient
  refine ⟨e.hom ≫ Q, ?_⟩
  exact hQ.comp (SmoothRep.hom_hom_surjective e)

end Langlands.Classification
