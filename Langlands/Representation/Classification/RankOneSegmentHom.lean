import Langlands.Representation.Classification.RankOneSegmentMatching
import Langlands.Representation.Classification.UniformJacquetTensorPiece
import Langlands.Representation.Classification.TwoSegmentShufflePieces
import Langlands.Representation.Classification.SegmentFullJacquetProof
import Langlands.Representation.Classification.SegmentSocleJacquetReduction
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.Tensor.FiniteProperties

/-! Actual geometric pieces and induction maps for matched rank-one segment factors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.RankOneSegmentHom

open GeneralLinear Geometric CuspidalSupport PadicField.TopologicalData CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem cast_trans {P : ℕ → Sort*} {a b c : ℕ}
    (h : a = b) (k : b = c) (x : P a) : k ▸ (h ▸ x) = (h.trans k) ▸ x := by
  subst b
  subst c
  rfl

/-- An actual representative of a twisted class is isomorphic to the corresponding
segment factor, including the necessary equality transport of the rank. -/
theorem factor_iso_of_twist_eq
    (ρ ρ' : CuspidalDatum.{uV, uF} T) (s : ℝ) (heq : ρ' = ρ.twist s)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (A' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ'.rank))
    (hA : ρ.IsRepresentedBy A) (hA' : ρ'.IsRepresentedBy A') :
    letI := T.topology
    Nonempty (((congrArg CuspidalDatum.rank heq) ▸ A'.obj :
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ρ.rank F.Carrier)) ≅ T.segmentFactor A.obj s) := by
  let := T.topology
  subst heq
  let B := SupercuspidalRep.twist (T.determinantPowerCharacter ρ.rank s)
    (T.isOpen_ker_determinantPowerCharacter ρ.rank s)
    (T.ker_determinant_le_ker_determinantPowerCharacter ρ.rank s) A
  have hcls : A'.isoClass = B.isoClass := by
    rw [hA']
    change T.supercuspidalClassRealPowerTwist ρ.rank s ρ.cls =
      T.supercuspidalClassRealPowerTwist ρ.rank s A.isoClass
    rw [hA]
  obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff A' B).mp hcls
  exact ⟨(supercuspidalProperty (F := F.Carrier) (n := ρ.rank)).ι.mapIso e⟩

/-- In a singleton block shape, the ambient coordinate of any block is its block number. -/
theorem index_val_of_size_eq_one {n : ℕ} (B : BlockShape n)
    (hB : ∀ j, B.size j = 1) (j : Fin B.length) (a : Fin (B.size j)) :
    (B.index j a : ℕ) = (j : ℕ) := by
  have ha : (a : ℕ) = 0 := by
    have : (a : ℕ) < 1 := lt_of_lt_of_eq a.isLt (hB j)
    omega
  change (finSigmaFinEquiv ⟨j, a⟩ : ℕ) = _
  rw [finSigmaFinEquiv_apply]
  simp [hB, ha]

/-- The rank-one cuspidal datum of an actual rank-one supercuspidal object. -/
def rankOneDatum
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := 1)) :
    CuspidalDatum.{uV, uF} T :=
  letI := T.topology
  ⟨1, Nat.one_pos, A.isoClass⟩

set_option maxHeartbeats 1200000 in
/-- A minimal occurrence matching identifies each geometric piece with the
external tensor of its actual rank-one target supercuspidal factors. -/
def pieceEquivOfMatching
    {m : ℕ} (d : T.SegmentProductDatum.{uV, uF} (m * 1))
    (hrank : ∀ j, (d.segments j).rank = 1) (hsoc : d.HasSegmentSocles)
    (X : letI := T.topology;
      Fin m → SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := 1))
    (w : MinimalRepresentatives d.shape (BlockShape.uniform m 1 Nat.one_pos))
    (hmatch : ∀ j (i : Fin (d.shape.size j)),
      (d.segments j).member (i : ℕ) =
        rankOneDatum F T (X (Fin.cast (Nat.mul_one m) (w.val (d.shape.index j i)))))
    (S : BlockRefinement d.shape) (R : BlockRefinement (BlockShape.uniform m 1 Nat.one_pos))
    (hS : IsIntersectionRefinement (F := F.Carrier) d.shape
      (BlockShape.uniform m 1 Nat.one_pos) w.val S)
    (hR : IsIntersectionRefinement (F := F.Carrier)
      (BlockShape.uniform m 1 Nat.one_pos) d.shape w.val⁻¹ R) :
    letI := T.topology
    ((geometricPieceFunctor T d.shape (BlockShape.uniform m 1 Nat.one_pos)
      w.val S R hS.2.1 hR.2.1).obj (FiniteTensor.externalSmoothObject d.blocks)).ρ.Equiv
        (FiniteTensor.external (fun t => (X t).obj.representation)) := by
  let := T.topology
  have hdiv : ∀ j i, 1 ∣ (S j).size i := fun _ _ => one_dvd _
  have hsize : ∀ j i, (S j).size i = 1 := fun j i =>
    ShuffleRefinement.source_size_eq_of_dvd Nat.one_pos d.shape w.val S hS.2.1 j i (hdiv j i)
  apply UniformJacquetTensorPiece.pieceEquiv F T Nat.one_pos d.shape d.blocks
    w.val w.property S R hS.2.1 hR.2.1 hdiv (fun t => (X t).obj)
  intro j
  let Δ := d.segments j
  let A := Δ.base.representative
  let targetIndex := ShuffleRefinement.refinementTargetIndex Nat.one_pos d.shape w.val S j
  let Y := fun i => ((hrank j).symm ▸ (X (targetIndex i)).obj :
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear Δ.rank F.Carrier))
  have hY : ∀ i, Nonempty (Y i ≅ T.segmentFactor A.obj (0 + ((i : ℕ) : ℝ))) := by
    intro i
    have hi := hmatch j ((S j).index i ⟨0, (S j).positive i⟩)
    rw [index_val_of_size_eq_one (S j) (hsize j)] at hi
    have hcoord := ShuffleRefinement.source_piece_coordinates Nat.one_pos d.shape w.val S
      hS.2.1 w.property j i (hdiv j i) ⟨0, (S j).positive i⟩
    have ht : Fin.cast (Nat.mul_one m)
        (w.val (d.shape.index j ((S j).index i ⟨0, (S j).positive i⟩))) = targetIndex i := by
      rw [hcoord]
      apply Fin.ext
      exact index_val_of_size_eq_one (BlockShape.uniform m 1 Nat.one_pos) (fun _ => rfl) _ _
    rw [ht] at hi
    have he := factor_iso_of_twist_eq F T Δ.base (rankOneDatum F T (X (targetIndex i)))
      ((i : ℕ) : ℝ) hi.symm A (X (targetIndex i)) Δ.base.isRepresentedBy_representative rfl
    let Z : SmoothRep.{0, uF, uV} ℂ (GeneralLinear Δ.rank F.Carrier) :=
      Eq.rec (motive := fun n _ => letI := T.topology;
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
        (X (targetIndex i)).obj (congrArg CuspidalDatum.rank hi.symm)
    have hZ : Z = Y i := by
      apply eq_of_heq
      simp only [Z, Y, heq_eq_eq]
    obtain ⟨e⟩ := he
    refine ⟨eqToIso hZ.symm ≪≫ e ≪≫ ?_⟩
    exact eqToIso (congrArg (T.segmentFactor A.obj) (zero_add _).symm)
  obtain ⟨H⟩ := TwoSegmentShuffle.segment_jacquet_equiv F T (segmentFullJacquetFormula F T).1
    A Δ.base.isRepresentedBy_representative 0 Δ (by simp) (d.blocks j)
    (hsoc j).isSegmentSubrepresentation (S j)
    (fun i => (hsize j i).trans (hrank j).symm) Y hY
  refine ⟨H.trans (FiniteTensorFiltration.externalCongr fun i => ?_)⟩
  apply SmoothRep.equivOfIso
  apply eqToIso
  apply eq_of_heq
  simp only [Y, targetIndex, heq_eq_eq]
  exact cast_trans (P := fun n => letI := T.topology;
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hrank j).symm ((hsize j i).trans (hrank j).symm).symm
    (X (targetIndex i)).obj

/-- A chosen nonzero map from a rank-one segment-socle product to the induction
of an actually matched cuspidal target tensor. -/
def inductionMapOfMatching
    {m : ℕ} (hm : 0 < m) (d : T.SegmentProductDatum.{uV, uF} (m * 1))
    (hrank : ∀ j, (d.segments j).rank = 1) (hsoc : d.HasSegmentSocles)
    (X : letI := T.topology;
      Fin m → SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := 1))
    (w : MinimalRepresentatives d.shape (BlockShape.uniform m 1 Nat.one_pos))
    (hmatch : ∀ j (i : Fin (d.shape.size j)),
      (d.segments j).member (i : ℕ) =
        rankOneDatum F T (X (Fin.cast (Nat.mul_one m) (w.val (d.shape.index j i))))) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m * 1)
    { f : d.induced.representation.IntertwiningMap
        (T.normalizedProductInduced (BlockShape.uniform m 1 Nat.one_pos)
          (fun t => (X t).obj.representation)) // f ≠ 0 } := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (m * 1)
  have hblocks j := (SegmentSocleJacquetReduction.isIrreducible_isAdmissible_of_isSegmentSocle
    T (d.segments j) (d.blocks j) (hsoc j)).2
  have hσ : (FiniteTensor.externalSmoothObject d.blocks).IsAdmissible :=
    FiniteTensor.isAdmissible_external _ hblocks
  have hτ := glCuspidalTensor.{uV, uF} p F T (m * 1) (Nat.mul_pos hm Nat.one_pos)
    (BlockShape.uniform m 1 Nat.one_pos) X
  exact nonzeroInductionMapOfPiece F T (Nat.mul_pos hm Nat.one_pos) d.shape
    (BlockShape.uniform m 1 Nat.one_pos) (FiniteTensor.externalSmoothObject d.blocks)
    (FiniteTensor.externalSmoothObject (fun t => (X t).obj)) hσ hτ.1 hτ.2 w
    (fun S R hS hR => ⟨pieceEquivOfMatching F T d hrank hsoc X w hmatch S R hS hR⟩)

/-- Equal cuspidal content and weakly decreasing target norms suffice for a
nonzero map from an arbitrary product of rank-one segment socles to the target
principal series, with all multiplicities retained. -/
def inductionMapOfContent
    {m : ℕ} (hm : 0 < m) (d : T.SegmentProductDatum.{uV, uF} (m * 1))
    (hrank : ∀ j, (d.segments j).rank = 1) (hsoc : d.HasSegmentSocles)
    (X : letI := T.topology;
      Fin m → SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := 1))
    (hcontent : d.multisegment.cuspidalContent = List.ofFn (fun t => rankOneDatum F T (X t)))
    (horder : Antitone (fun t => (rankOneDatum F T (X t)).scalarUniformizerNorm)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m * 1)
    { f : d.induced.representation.IntertwiningMap
        (T.normalizedProductInduced (BlockShape.uniform m 1 Nat.one_pos)
          (fun t => (X t).obj.representation)) // f ≠ 0 } := by
  let := T.topology
  let target : Fin (m * 1) → CuspidalDatum.{uV, uF} T := fun i =>
    rankOneDatum F T (X (Fin.cast (Nat.mul_one m) i))
  have hct : d.multisegment.cuspidalContent = List.ofFn target :=
    hcontent.trans (congrArg (fun l : List (CuspidalDatum.{uV, uF} T) =>
      (l : Multiset (CuspidalDatum.{uV, uF} T)))
      (List.ofFn_congr (Nat.mul_one m).symm (fun t => rankOneDatum F T (X t))))
  have ht : Antitone (fun t => (target t).scalarUniformizerNorm) := by
    intro i j hij
    exact horder (show Fin.cast (Nat.mul_one m) i ≤ Fin.cast (Nat.mul_one m) j from hij)
  let h := RankOneSegmentMatching.exists_minimal_matching d hrank
    (BlockShape.uniform m 1 Nat.one_pos) (fun _ => rfl) target hct ht
  exact inductionMapOfMatching F T hm d hrank hsoc X h.choose h.choose_spec

end Langlands.Classification.RankOneSegmentHom
