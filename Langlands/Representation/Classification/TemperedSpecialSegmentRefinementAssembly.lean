import Langlands.Representation.Classification.TemperedSpecialSegmentRefinementAssemblyStatement
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.LinkedSegmentHeadExponentStatement
import Langlands.Representation.Classification.TwistedProductCharacterTwistProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof

/-! Conditional development of tempered special-segment refinement.
The analytic exhaustion, individual-head classification, exponent comparison,
and ordered regrouping inputs are kept explicit. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private def segmentFactorZeroIso {n : ℕ}
    (σ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) :
    letI := T.topology
    T.segmentFactor σ 0 ≅ σ := by
  letI := T.topology
  exact SmoothRep.mkIso (equivOfRepresentationEq
    (realPowerTwist_zero (T.determinantNorm n) σ.representation))

private def twistedUnitaryExponent {n : ℕ}
    (σ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hσ : letI := T.topology; IsUnitarizable σ.representation) (s : ℝ) :
    letI := T.topology
    UnitaryExponentData (T.determinantNorm n) (T.segmentFactor σ s).representation := by
  letI := T.topology
  let u : UnitaryExponentData (T.determinantNorm n) σ.representation :=
    ⟨0, by simpa only [neg_zero, realPowerTwist_zero] using hσ.some⟩
  exact u.shift s

private theorem twistedUnitaryExponent_exponent {n : ℕ}
    (σ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hσ : letI := T.topology; IsUnitarizable σ.representation) (s : ℝ) :
    (twistedUnitaryExponent F T σ hσ s).exponent = s :=
  zero_add s

private def commonRealTwistProductIso {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : ℝ) :
    letI := T.topology
    T.segmentFactor ((T.normalizedProductInductionFunctor B).obj σ) s ≅
      (T.normalizedProductInductionFunctor B).obj (fun i => T.segmentFactor (σ i) s) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨realPowerCharacter T.normalizedAbsUnits s,
      isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s⟩
  let σχ := fun i => (σ i).twist
    (χ.toMonoidHom.comp determinant)
    (χ.isOpen_ker.preimage (T.generalLinearDeterminant (B.size i)).continuous)
  let z : T.twistedProductInduced B σ (fun _ => 0) ≅
      (T.normalizedProductInductionFunctor B).obj σ :=
    (T.normalizedProductInductionFunctor B).mapIso
      (Pi.isoMk fun i => segmentFactorZeroIso F T (σ i))
  let zχ : T.twistedProductInduced B σχ (fun _ => 0) ≅
      (T.normalizedProductInductionFunctor B).obj σχ :=
    (T.normalizedProductInductionFunctor B).mapIso
      (Pi.isoMk fun i => segmentFactorZeroIso F T (σχ i))
  let e := (twistedProductCharacterTwist.{uF,max uF uV} F T n hn B χ σ
    (fun _ => 0)).some
  exact (SmoothRep.twistIso (T.determinantPowerCharacter n s)
    (T.isOpen_ker_determinantPowerCharacter n s) z.symm) ≪≫
    SmoothRep.mkIso e ≪≫ zχ

private def rankTransportUnitaryExponent {n m : ℕ} (h : n = m)
    (σ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (u : letI := T.topology
      UnitaryExponentData (T.determinantNorm n) σ.representation) :
    letI := T.topology
    UnitaryExponentData (T.determinantNorm m) (h ▸ σ).representation := by
  subst m
  exact u

private theorem rankTransportUnitaryExponent_exponent {n m : ℕ} (h : n = m)
    (σ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (u : letI := T.topology
      UnitaryExponentData (T.determinantNorm n) σ.representation) :
    (rankTransportUnitaryExponent F T h σ u).exponent = u.exponent := by
  subst m
  rfl

private structure TemperedBlockSegmentData {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (s : ℝ) where
  datum : T.SegmentProductDatum.{max uF uV,uF} n
  heads : datum.HasSegmentHeads
  unitaryExponent : ∀ i, letI := T.topology
    UnitaryExponentData (T.determinantNorm (datum.segments i).degree)
      (datum.blocks i).representation
  exponent_eq : ∀ i, (unitaryExponent i).exponent = s
  inducedIso : letI := T.topology
    datum.induced ≅ T.segmentFactor π s

private def productRankIso {n : ℕ} (B : BlockShape n)
    (size : Fin B.length → ℕ) (hsize : ∀ i, size i = B.size i)
    (positive : ∀ i, 0 < size i) (sum_eq : ∑ i, size i = n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (⟨B.length, size, positive, sum_eq⟩ : BlockShape n)).obj
      (fun i => ((hsize i).symm ▸ σ i :
        SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (size i) F.Carrier))) ≅
        (T.normalizedProductInductionFunctor B).obj σ := by
  have hs : size = B.size := funext hsize
  subst size
  exact Iso.refl _

set_option maxHeartbeats 800000 in
private theorem refineTemperedBlock
    (exhaustion : TemperedBlockExhaustion.{uF,uV} F T)
    (classification : SegmentEssentialSquareIntegrableClassification.{uF,uV} F T)
    {n : ℕ} (hn : 0 < n)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; Representation.IsIrreducible π.representation)
    (ht : letI := T.topology; T.IsTempered π.representation)
    (s : ℝ) : Nonempty (TemperedBlockSegmentData F T π s) := by
  classical
  let := T.topology
  obtain ⟨B, σ, hσ, ⟨e⟩⟩ := exhaustion n hn π hπ ht
  have hc (i : Fin B.length) :
      ∃ (Δ : T.Segment.{max uF uV,uF}) (h : Δ.degree = B.size i),
        T.IsSegmentHead Δ (h.symm ▸ T.segmentFactor (σ i) s) := by
    apply (classification (B.size i) (B.positive i) (T.segmentFactor (σ i) s) ?_).mp
    · exact (hσ i).2.1.isEssentiallySquareIntegrable.realPowerTwist s
    · exact (SmoothRep.isIrreducible_twist_iff _ _ (σ i)).mpr (hσ i).1
  choose Δ h hhead using hc
  have hsum : ∑ i, (Δ i).degree = n :=
    (Finset.sum_congr rfl fun i _ => h i).trans B.sum_eq
  let d : T.SegmentProductDatum.{max uF uV,uF} n :=
    ⟨B.length, Δ, hsum, fun i => (h i).symm ▸ T.segmentFactor (σ i) s⟩
  let u := fun i => rankTransportUnitaryExponent F T (h i).symm
    (T.segmentFactor (σ i) s) (twistedUnitaryExponent F T (σ i) (hσ i).2.2 s)
  have eind : d.induced ≅
      (T.normalizedProductInductionFunctor B).obj (fun i => T.segmentFactor (σ i) s) :=
    productRankIso F T B _ h _ hsum (fun i => T.segmentFactor (σ i) s)
  refine ⟨⟨d, hhead, u, ?_, ?_⟩⟩
  · intro i
    exact (rankTransportUnitaryExponent_exponent F T _ _ _).trans
      (twistedUnitaryExponent_exponent F T _ _ _)
  · exact eind ≪≫ (commonRealTwistProductIso F T hn B σ s).symm ≪≫
      (SmoothRep.twistIso (T.determinantPowerCharacter n s)
        (T.isOpen_ker_determinantPowerCharacter n s) e.symm)

private def flattenSegmentData {n : ℕ} (B : BlockShape n)
    (ds : ∀ i, T.SegmentProductDatum.{max uF uV,uF} (B.size i)) :
    T.SegmentProductDatum.{max uF uV,uF} n :=
  let S := fun i => (ds i).shape
  let e := B.flattenBlockEquiv S
  { length := (B.flatten S).length
    segments := fun k => (ds (e.symm k).1).segments (e.symm k).2
    degree_sum := (B.flatten S).sum_eq
    blocks := fun k => (ds (e.symm k).1).blocks (e.symm k).2 }

private def reindexRankIso {ι : Type} (r : ι → ℕ)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (r i) F.Carrier))
    {i j : ι} (h : i = j) :
    letI := T.topology
    (congrArg r h ▸ σ i) ≅ σ j := by
  subst j
  exact Iso.refl _

set_option maxHeartbeats 400000 in
private theorem flattenSegmentData_inducedIso
    (regrouping : Parabolic.OrderedProductRegrouping.{uF,max uF uV} F T)
    {n : ℕ} (B : BlockShape n)
    (ds : ∀ j, T.SegmentProductDatum.{max uF uV,uF} (B.size j)) :
    letI := T.topology
    Nonempty ((flattenSegmentData F T B ds).induced ≅
      (T.normalizedProductInductionFunctor B).obj (fun j => (ds j).induced)) := by
  let := T.topology
  let S := fun j => (ds j).shape
  let e := B.flattenBlockEquiv S
  let d := flattenSegmentData F T B ds
  let h (q : (j : Fin B.length) × Fin (S j).length) :
      (S q.1).size q.2 = d.shape.size (e q) :=
    (B.flatten_size_flattenBlockEquiv S q).symm
  obtain ⟨ereg⟩ := regrouping n d.shape B S e h
    (fun j k x => B.index_index_eq_flatten S ⟨j,k⟩ x) d.blocks
  have einner (j : Fin B.length) :
      (T.normalizedProductInductionFunctor (S j)).obj
        (fun k => (h ⟨j,k⟩).symm ▸ d.blocks (e ⟨j,k⟩)) ≅ (ds j).induced := by
    apply (T.normalizedProductInductionFunctor (S j)).mapIso
    apply Pi.isoMk
    intro k
    exact reindexRankIso F T
      (fun q : (j : Fin B.length) × Fin (S j).length => (S q.1).size q.2)
      (fun q => (ds q.1).blocks q.2) (e.symm_apply_apply ⟨j,k⟩)
  exact ⟨ereg ≪≫ (T.normalizedProductInductionFunctor B).mapIso (Pi.isoMk einner)⟩

set_option maxHeartbeats 800000 in
/-- Conditional assembly; the four inputs are separate Library propositions. -/
theorem temperedSpecialSegmentRefinementAssembly :
    TemperedSpecialSegmentRefinementAssembly.{uF,uV} F T := by
  intro exhaustion classification comparison regrouping
  classical
  let := T.topology
  intro n hn t
  let a (j : Fin t.shape.length) := Classical.choice
    (refineTemperedBlock F T exhaustion classification (t.shape.positive j)
      (t.blocks j) (t.irreducible j) (t.tempered j) (t.exponent j))
  let ds := fun j => (a j).datum
  let S := fun j => (ds j).shape
  let e := t.shape.flattenBlockEquiv S
  let d := flattenSegmentData F T t.shape ds
  have hheads : d.HasSegmentHeads := fun i => (a (e.symm i).1).heads (e.symm i).2
  have hordered : d.IsPrecedenceOrdered := by
    intro i j hij hp
    have hlabel : e (e.symm i) < e (e.symm j) := by
      rw [e.apply_symm_apply, e.apply_symm_apply]
      exact hij
    have hparent : (e.symm i).1 ≤ (e.symm j).1 := by
      rcases (t.shape.flattenBlockEquiv_lt_iff S _ _).mp hlabel with h | ⟨h, _⟩
      · exact h.le
      · exact le_of_eq h
    have he := (comparison (d.segments i) (d.segments j) (d.blocks i) (d.blocks j)
      (hheads i) (hheads j)
      ((a (e.symm i).1).unitaryExponent (e.symm i).2)
      ((a (e.symm j).1).unitaryExponent (e.symm j).2)).2 hp
    have hexpi := (a (e.symm i).1).exponent_eq (e.symm i).2
    have hexpj := (a (e.symm j).1).exponent_eq (e.symm j).2
    have he' : t.exponent (e.symm i).1 < t.exponent (e.symm j).1 :=
      hexpi.symm.trans_lt (he.trans_eq hexpj)
    exact (not_lt_of_ge (t.strictAnti.antitone hparent)) he'
  obtain ⟨eflat⟩ := flattenSegmentData_inducedIso F T regrouping t.shape ds
  have efinal :
      (T.normalizedProductInductionFunctor t.shape).obj
        (fun j => (ds j).induced) ≅ t.standardModule :=
    (T.normalizedProductInductionFunctor t.shape).mapIso
      (Pi.isoMk fun j => (a j).inducedIso)
  exact ⟨d, hordered, hheads, ⟨eflat ≪≫ efinal⟩⟩

end Langlands.Classification
