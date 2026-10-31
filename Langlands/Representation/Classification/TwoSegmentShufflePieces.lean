import Langlands.Representation.Classification.SegmentFullJacquetStatement
import Langlands.Representation.Classification.JuxtaposedRefinementTools
import Langlands.Representation.Classification.UniformRefinementLeviTransport
import Langlands.Representation.Geometric.WholeLeviPieceTransport
import Langlands.Representation.CuspidalSupport.LeviAssociation

/-! Geometric pieces of the uniform Jacquet module of two segment socles. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.TwoSegmentShuffle

open GeneralLinear Geometric CuspidalSupport CategoryTheory PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A block shape all of whose blocks have size `r` is the uniform shape. -/
theorem eq_uniform_of_size_eq {m r : ℕ} (hr : 0 < r) (D : BlockShape (m * r))
    (hD : ∀ i, D.size i = r) : D = BlockShape.uniform m r hr := by
  have hsum : D.length * r = m * r := by
    calc
      D.length * r = ∑ i : Fin D.length, D.size i := by simp [hD]
      _ = m * r := D.sum_eq
  exact BlockShape.ext_of_size (Nat.eq_of_mul_eq_mul_right hr hsum) (fun i => hD i)

/-- Conditional on Zelevinsky 1980, 3.1: the normalized Jacquet module of a segment
subrepresentation along a shape with all blocks of the cuspidal rank is the tensor
product of any family of factors isomorphic to the increasing segment factors, each
transported to the block size. -/
theorem segment_jacquet_equiv
    (h31 : SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    {ρ : CuspidalDatum.{uV, uF} T}
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (a : ℝ) (Δ : Segment.{uV, uF} T)
    (hbase : Δ.base = ρ.twist a)
    (Y : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hY : T.IsSegmentSubrepresentation Δ Y)
    (D : BlockShape Δ.degree) (hD : ∀ i, D.size i = ρ.rank)
    (X : letI := T.topology;
      ∀ _ : Fin D.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ρ.rank F.Carrier))
    (hX : letI := T.topology;
      ∀ i, Nonempty (X i ≅ T.segmentFactor A.obj (a + ((i : ℕ) : ℝ)))) :
    letI := T.topology
    Nonempty (((T.normalizedJacquetFunctor D).obj Y).representation.Equiv
      (FiniteTensor.external (fun i => ((hD i).symm ▸ X i :
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size i) F.Carrier)).representation))) := by
  let := T.topology
  obtain ⟨base, len, hlen⟩ := Δ
  dsimp only at hbase
  subst hbase
  obtain rfl := eq_uniform_of_size_eq ρ.rank_pos D hD
  obtain ⟨A', hA', -⟩ := id hY
  obtain ⟨e31⟩ := h31 ⟨ρ.twist a, len, hlen⟩ A' Y hA' hY
  have hf : ∀ i, Nonempty ((T.segmentFactors A'.obj len ρ.rank_pos i).representation.Equiv
      (X i).representation) := by
    intro i
    obtain ⟨eX⟩ := hX i
    rw [add_comm a] at eX
    obtain ⟨f⟩ := JuxtaposedShuffle.nonempty_cast_iso T A hA a rfl A' hA' rfl _ (X i) eX
    exact ⟨SmoothRep.equivOfIso f.symm⟩
  exact ⟨e31.trans (FiniteTensorFiltration.externalCongr fun i => (hf i).some)⟩

set_option maxHeartbeats 1000000 in
/-- Conditional on Zelevinsky 1980, 3.1: an equivalence from the geometric piece
of a minimal representative whose source refinement has all pieces divisible by
the cuspidal rank to the tensor product of any target family whose factor at the
image of piece `i` of block `j` is isomorphic to `ν^(a_j + i) A`. -/
def pieceEquiv
    (h31 : SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    {ρ : CuspidalDatum.{uV, uF} T}
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) {m : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} (m * ρ.rank))
    (a : Fin d.length → ℝ) (hbase : ∀ j, (d.segments j).base = ρ.twist (a j))
    (hsub : ∀ j, T.IsSegmentSubrepresentation (d.segments j) (d.blocks j))
    (w : Equiv.Perm (Fin (m * ρ.rank)))
    (hw : IsMinimalRepresentative d.shape (BlockShape.uniform m ρ.rank ρ.rank_pos) w)
    (S : BlockRefinement d.shape) (R : BlockRefinement (BlockShape.uniform m ρ.rank ρ.rank_pos))
    (hS : sourceLevi F.Carrier d.shape (BlockShape.uniform m ρ.rank ρ.rank_pos) w =
      refinedLevi F.Carrier d.shape S)
    (hR : sourceLevi F.Carrier (BlockShape.uniform m ρ.rank ρ.rank_pos) d.shape w⁻¹ =
      refinedLevi F.Carrier (BlockShape.uniform m ρ.rank ρ.rank_pos) R)
    (hdiv : ∀ j i, ρ.rank ∣ (S j).size i)
    (X : letI := T.topology;
      Fin m → SmoothRep.{0, uF, uV} ℂ (GeneralLinear ρ.rank F.Carrier))
    (hX : letI := T.topology; ∀ j i,
      Nonempty (X (ShuffleRefinement.refinementTargetIndex ρ.rank_pos d.shape w S j i) ≅
        T.segmentFactor A.obj (a j + ((i : ℕ) : ℝ)))) :
    letI := T.topology
    ((geometricPieceFunctor T d.shape (BlockShape.uniform m ρ.rank ρ.rank_pos)
        w S R hS hR).obj (FiniteTensor.externalSmoothObject d.blocks)).ρ.Equiv
      (FiniteTensor.external (fun t => (X t).representation)) := by
  let := T.topology
  let C := BlockShape.uniform m ρ.rank ρ.rank_pos
  have hc := ShuffleRefinement.conjugatesLevi_flatten_uniform ρ.rank_pos d.shape w S hS hdiv
  let τ := fun j i =>
    ((ShuffleRefinement.source_size_eq_of_dvd ρ.rank_pos d.shape w S hS j i (hdiv j i)).symm ▸
      X (ShuffleRefinement.refinementTargetIndex ρ.rank_pos d.shape w S j i) :
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S j).size i) F.Carrier))
  have H : ∀ j, (T.normalizedJacquet (S j) (d.blocks j).obj.ρ).Equiv
      (FiniteTensor.external (fun i => (τ j i).representation)) := fun j =>
    (segment_jacquet_equiv F T h31 A hA (a j) (d.segments j) (hbase j) (d.blocks j) (hsub j)
      (S j) (fun i => ShuffleRefinement.source_size_eq_of_dvd ρ.rank_pos d.shape w S hS j i
        (hdiv j i))
      (fun i => X (ShuffleRefinement.refinementTargetIndex ρ.rank_pos d.shape w S j i))
      (hX j)).some
  let X' := FiniteTensor.external
    (fun j => FiniteTensor.external (fun i => (τ j i).representation))
  let e1 := wholeLeviGeometricPieceEquiv T d.shape C w S R hS hR hc
    (FiniteTensor.externalSmoothObject d.blocks)
  let e2 := (RefinedJacquetTensor.jacquetEquiv T d.shape S (fun j => (d.blocks j).obj)).trans
    (FiniteTensorFiltration.compCongr (FiniteTensorFiltration.externalCongr H)
      (refinedLeviEquiv F.Carrier d.shape S).symm.toMonoidHom)
  let e3 : Representation.Equiv ((X'.comp (refinedLeviEquiv F.Carrier d.shape S).symm.toMonoidHom).comp
      (flattenedLeviEquiv F.Carrier d.shape S).toMonoidHom)
      (X'.comp (flattenedLeviProductEquiv F.Carrier d.shape S).toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
      apply LinearMap.ext
      intro v
      simp [flattenedLeviEquiv])
  let e4 := CuspidalSupport.transportEquiv w hc
    ((FiniteTensorFiltration.compCongr e2
      (flattenedLeviEquiv F.Carrier d.shape S).toMonoidHom).trans e3)
  let e5 := (ShuffleRefinement.uniformRefinementTensorEquiv F T ρ.rank_pos d.shape w S hS hw
    hdiv X).symm
  exact e1.trans (e4.trans e5)

/-- Conditional on Zelevinsky 1980, 3.1: for two segment socles on one cuspidal
line, the geometric piece of a minimal representative whose source refinement has
all pieces divisible by the cuspidal rank is the shuffle tensor of the shuffle
attached to that representative. -/
theorem surviving_piece_equiv
    (h31 : SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    {ρ : CuspidalDatum.{uV, uF} T}
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (a₀ a₁ : ℝ) {m₀ m₁ : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} ((m₀ + m₁) * ρ.rank)) (h₂ : d.length = 2)
    (hsoc : d.HasSegmentSocles)
    (hbase0 : (d.segments ⟨0, by omega⟩).base = ρ.twist a₀)
    (hbase1 : (d.segments ⟨1, by omega⟩).base = ρ.twist a₁)
    (h₀ : d.shape.size (Fin.cast h₂.symm 0) = m₀ * ρ.rank)
    (h₁ : d.shape.size (Fin.cast h₂.symm 1) = m₁ * ρ.rank)
    (w : MinimalRepresentatives d.shape (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos))
    (S : BlockRefinement d.shape)
    (R : BlockRefinement (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos))
    (hS : IsIntersectionRefinement (F := F.Carrier) d.shape
      (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) w.val S)
    (hR : IsIntersectionRefinement (F := F.Carrier)
      (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) d.shape w.val⁻¹ R)
    (hdiv : ∀ j i, ρ.rank ∣ (S j).size i) :
    letI := T.topology
    Nonempty (((geometricPieceFunctor T d.shape (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos)
        w.val S R hS.2.1 hR.2.1).obj (FiniteTensor.externalSmoothObject d.blocks)).ρ.Equiv
      (FiniteTensor.externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos
        (ShuffleRefinement.refinementShuffle ρ.rank_pos d.shape h₂ h₀ h₁ w.val S hS.2.1
          w.property hdiv).val a₀ a₁)).representation) := by
  let := T.topology
  have hj : ∀ j : Fin d.length, j = Fin.cast h₂.symm 0 ∨ j = Fin.cast h₂.symm 1 := by
    intro j
    rcases j with ⟨j, hj⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (h₂ ▸ hj : j < 2) with h | h
    · exact Or.inl (Fin.ext (by simp; omega))
    · exact Or.inr (Fin.ext (by simp [h]))
  let a : Fin d.length → ℝ := fun j => if (j : ℕ) = 0 then a₀ else a₁
  have hbase : ∀ j, (d.segments j).base = ρ.twist (a j) := by
    intro j
    rcases hj j with rfl | rfl
    · exact hbase0
    · exact hbase1
  exact ⟨pieceEquiv F T h31 A hA d a hbase (fun j => (hsoc j).isSegmentSubrepresentation)
    w.val w.property S R hS.2.1 hR.2.1 hdiv _ (by
      intro j i
      rcases hj j with rfl | rfl
      · exact ⟨eqToIso (congrArg (T.segmentFactor A.obj)
          (ShuffleRefinement.shuffleExponent_refinementTargetIndex_zero ρ.rank_pos d.shape h₂
            h₀ h₁ w.val S hS.2.1 w.property hdiv a₀ a₁ i))⟩
      · exact ⟨eqToIso (congrArg (T.segmentFactor A.obj)
          (ShuffleRefinement.shuffleExponent_refinementTargetIndex_one ρ.rank_pos d.shape h₂
            h₀ h₁ w.val S hS.2.1 w.property hdiv a₀ a₁ i))⟩)⟩

end Langlands.Classification.TwoSegmentShuffle
