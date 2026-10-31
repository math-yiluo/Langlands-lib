import Langlands.Representation.Classification.TwoSegmentSocleShuffleJacquetStatement
import Langlands.Representation.Classification.UniformJacquetVanishing
import Langlands.Representation.Classification.UniformRefinementSurvivors
import Langlands.Representation.Classification.UniformRefinementShuffleRealization
import Langlands.Representation.Classification.SegmentEdgeJacquetReduction
import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof

/-!
# Assembly of the shuffle Jacquet filtration of two segment socles

The normalized geometric lemma filters the uniform Jacquet module of a product
of two segment socles by the minimal double-coset representatives. This module
deletes the pieces whose source refinement has a piece of size not divisible by
the cuspidal rank, indexes the remaining pieces by shuffle subsets, and counts
composition factors. The identification of each remaining piece with its
shuffle tensor is an explicit hypothesis here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.TwoSegmentShuffle

open GeneralLinear Geometric CuspidalSupport CategoryTheory PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A geometric piece of a product of segment socles vanishes when some piece
of its source refinement has size not divisible by the common cuspidal rank. -/
theorem geometricPiece_subsingleton_of_not_dvd {n : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} n) (hsoc : d.HasSegmentSocles) (r : ℕ)
    (hrank : ∀ j, (d.segments j).rank = r) (C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement d.shape) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier d.shape C w = refinedLevi F.Carrier d.shape S)
    (hR : sourceLevi F.Carrier C d.shape w⁻¹ = refinedLevi F.Carrier C R)
    (hdiv : ¬ ∀ j i, r ∣ (S j).size i) :
    letI := T.topology
    Subsingleton ((geometricPieceFunctor T d.shape C w S R hS hR).obj
      (FiniteTensor.externalSmoothObject d.blocks)) := by
  let := T.topology
  push Not at hdiv
  obtain ⟨j, i, hji⟩ := hdiv
  apply SegmentEdge.geometricPiece_subsingleton T d.shape C w S R hS hR
  apply SegmentEdge.refinedJacquet_external_subsingleton T d.shape S d.blocks j
  exact (hsoc j).jacquet_subsingleton_of_not_dvd T (S j) ⟨i, by rw [hrank j]; exact hji⟩

/-- The external tensor of the shuffle factors of an actual supercuspidal
representative is irreducible. -/
theorem shuffleTensor_isIrreducible {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (m : ℕ) (hm : 0 < m) (S : Finset (Fin m)) (a₀ a₁ : ℝ) :
    letI := T.topology
    Representation.IsIrreducible
      (FiniteTensor.externalSmoothObject (shuffleFactors F T A.obj m hr S a₀ a₁)).representation := by
  let := T.topology
  exact (glCuspidalTensor.{uV, uF} p F T (m * r) (Nat.mul_pos hm hr)
    (BlockShape.uniform m r hr)
    (fun i => SupercuspidalRep.twist
      (T.determinantPowerCharacter r (shuffleExponent S a₀ a₁ i))
      (T.isOpen_ker_determinantPowerCharacter r _)
      (T.ker_determinant_le_ker_determinantPowerCharacter r _) A)).1

/-- The number of subsets of `Fin (m₀ + m₁)` with `m₀` elements. -/
theorem card_shuffles (m₀ m₁ : ℕ) :
    Nat.card {S : Finset (Fin (m₀ + m₁)) // S.card = m₀} = (m₀ + m₁).choose m₀ := by
  rw [Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

set_option maxHeartbeats 1600000 in
/-- The shuffle Jacquet multiplicities of two segment socles, given the
identification of every geometric piece with divisible source refinement with
its shuffle tensor. The rank and size equalities record the shape of `d`. -/
theorem shuffleJacquet_of_pieces :
    letI := T.topology
    ∀ (ρ : CuspidalDatum.{uV, uF} T)
      (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
      (a₀ a₁ : ℝ) (m₀ m₁ : ℕ)
      (d : T.SegmentProductDatum.{uV, uF} ((m₀ + m₁) * ρ.rank)) (h₂ : d.length = 2),
      d.HasSegmentSocles → (∀ j, (d.segments j).rank = ρ.rank) →
      ∀ (h₀ : d.shape.size (Fin.cast h₂.symm 0) = m₀ * ρ.rank)
        (h₁ : d.shape.size (Fin.cast h₂.symm 1) = m₁ * ρ.rank),
      (∀ (w : MinimalRepresentatives d.shape
          (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos))
        (S : BlockRefinement d.shape)
        (R : BlockRefinement (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos))
        (hS : IsIntersectionRefinement (F := F.Carrier) d.shape
          (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) w.val S)
        (hR : IsIntersectionRefinement (F := F.Carrier)
          (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) d.shape w.val⁻¹ R)
        (hdiv : ∀ j i, ρ.rank ∣ (S j).size i),
        Nonempty (((geometricPieceFunctor T d.shape
            (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) w.val S R hS.2.1 hR.2.1).obj
            (FiniteTensor.externalSmoothObject d.blocks)).ρ.Equiv
          (FiniteTensor.externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos
            (ShuffleRefinement.refinementShuffle ρ.rank_pos d.shape h₂ h₀ h₁ w.val S hS.2.1
              w.property hdiv).val a₀ a₁)).representation)) →
        let C := BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos
        let J := CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj
        HasCompositionSeriesLength J ((m₀ + m₁).choose m₀) ∧
          ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
            (τ : Representation ℂ (C.Levi F.Carrier) W),
            Representation.IsIrreducible τ →
              ∀ m : ℕ, HasJordanHolderMultiplicity J (Rep.of τ) m ↔
                m = Nat.card {S : Finset (Fin (m₀ + m₁)) // S.card = m₀ ∧
                  Nonempty ((FiniteTensor.externalSmoothObject
                    (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S a₀ a₁)).representation.Equiv
                      τ)} := by
  let := T.topology
  intro ρ A a₀ a₁ m₀ m₁ d h₂ hsoc hrank h₀ h₁ hpiece C J
  have hm₀ : 0 < m₀ := by
    have h := d.shape.positive (Fin.cast h₂.symm 0)
    rw [h₀] at h
    exact Nat.pos_of_mul_pos_right h
  have hn : 0 < (m₀ + m₁) * ρ.rank := Nat.mul_pos (by omega) ρ.rank_pos
  obtain ⟨S, R, hS, hR, M, e, order, s, hs⟩ :=
    padicGeometricLemma.{uF, max uF uV} p F T _ hn d.shape C
  let enum : Fin M ≃ MinimalRepresentatives d.shape C := order.trans e
  let ρY := FiniteTensor.externalSmoothObject d.blocks
  let evaluated := objectFiltrationAt s ρY
  have graded (i : Fin M) :
      Nonempty ((evaluated.gradedRepresentation i).ρ.Equiv
        ((geometricPieceFunctor T d.shape C (enum i).val (S (enum i))
          (R (enum i)) (hS (enum i)).2.1 (hR (enum i)).2.1).obj ρY).ρ) := by
    obtain ⟨iso⟩ := hs i
    exact ⟨Representation.equivOfIso (iso.app ρY)⟩
  let P : Fin M → Prop := fun i => ∀ j k, ρ.rank ∣ (S (enum i) j).size k
  have zero (i : Fin M) (hi : ¬ P i) : Subsingleton (evaluated.gradedRepresentation i) := by
    have hP := geometricPiece_subsingleton_of_not_dvd F T d hsoc ρ.rank hrank C (enum i).val
      (S (enum i)) (R (enum i)) (hS (enum i)).2.1 (hR (enum i)).2.1 hi
    obtain ⟨f⟩ := graded i
    exact @Function.Injective.subsingleton _ _ _ f.toLinearEquiv.injective hP
  obtain ⟨N, retained, t, ht⟩ :=
    ObjectRepFiltration.zeroFactorDeletionTheorem ℂ (C.Levi F.Carrier) _ M evaluated P zero
  let I := {S : Finset (Fin (m₀ + m₁)) // S.card = m₀}
  let selected : {i : Fin M // P i} ≃
      ShuffleRefinement.DivisibleRefinementRepresentatives ρ.rank_pos d.shape S :=
    enum.subtypeEquiv (fun _ => Iff.rfl)
  let indexing : Fin N ≃ I := (retained.trans selected).trans
    (ShuffleRefinement.divisibleEquivShuffles ρ.rank_pos d.shape h₂ h₀ h₁ S
      (fun w => (hS w).2.1))
  let family : I → Rep.{uV} ℂ (C.Levi F.Carrier) := fun S =>
    Rep.of (FiniteTensor.externalSmoothObject
      (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S.val a₀ a₁)).representation
  have hfamily : ∀ S, Representation.IsIrreducible (family S).ρ := fun S =>
    shuffleTensor_isIrreducible F T ρ.rank_pos A (m₀ + m₁) (by omega) S.val a₀ a₁
  have hgr : ∀ i, Nonempty ((t.gradedRepresentation i).ρ.Equiv (family (indexing i)).ρ) := by
    intro i
    obtain ⟨f⟩ := ht i
    obtain ⟨g⟩ := graded (retained i).val
    obtain ⟨h⟩ := hpiece (enum (retained i).val) (S _) (R _) (hS _) (hR _)
      (retained i).property
    exact ⟨(f.trans g).trans h⟩
  obtain ⟨hlen, hmult⟩ :=
    finiteFamilyFiltrationMultiplicity ℂ (C.Levi F.Carrier) I _ family hfamily N indexing t hgr
  refine ⟨?_, ?_⟩
  · rw [← card_shuffles m₀ m₁]
    exact hlen
  · intro W _ _ τ _ m
    change HasJordanHolderMultiplicity ((jacquetInductionFunctor T d.shape C).obj ρY)
      (Rep.of τ) m ↔ _
    rw [hmult (Rep.of τ) m]
    apply Iff.of_eq
    congr 1
    apply Nat.card_congr
    exact Equiv.subtypeSubtypeEquivSubtypeInter
      (fun S : Finset (Fin (m₀ + m₁)) => S.card = m₀)
      (fun S => Nonempty ((FiniteTensor.externalSmoothObject
        (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S a₀ a₁)).representation.Equiv τ))

/-- The interface supplied by the piece computation: for two segment socles on
one cuspidal line, every geometric piece of `r_C(⟨Δ₀⟩ × ⟨Δ₁⟩)` whose source
refinement has all piece sizes divisible by the cuspidal rank is equivalent to
the shuffle tensor of its subset `refinementShuffle`. The hypotheses are those
of `TwoSegmentSocleShuffleJacquet`, together with the two size equalities of
`d.shape` that `refinementShuffle` takes as arguments. -/
def SurvivingPieceEquiv : Prop :=
  letI := T.topology
  ∀ (ρ : CuspidalDatum.{uV, uF} T)
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (a₀ a₁ : ℝ) (m₀ m₁ : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((m₀ + m₁) * ρ.rank)) (h₂ : d.length = 2),
    ρ.IsRepresentedBy A → d.HasSegmentSocles →
    (d.segments ⟨0, by omega⟩).base = ρ.twist a₀ →
    (d.segments ⟨0, by omega⟩).length = m₀ →
    (d.segments ⟨1, by omega⟩).base = ρ.twist a₁ →
    (d.segments ⟨1, by omega⟩).length = m₁ →
    ∀ (h₀ : d.shape.size (Fin.cast h₂.symm 0) = m₀ * ρ.rank)
      (h₁ : d.shape.size (Fin.cast h₂.symm 1) = m₁ * ρ.rank)
      (w : MinimalRepresentatives d.shape (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos))
      (S : BlockRefinement d.shape)
      (R : BlockRefinement (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos))
      (hS : IsIntersectionRefinement (F := F.Carrier) d.shape
        (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) w.val S)
      (hR : IsIntersectionRefinement (F := F.Carrier)
        (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) d.shape w.val⁻¹ R)
      (hdiv : ∀ j i, ρ.rank ∣ (S j).size i),
      Nonempty (((geometricPieceFunctor T d.shape
          (BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos) w.val S R hS.2.1 hR.2.1).obj
          (FiniteTensor.externalSmoothObject d.blocks)).ρ.Equiv
        (FiniteTensor.externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos
          (ShuffleRefinement.refinementShuffle ρ.rank_pos d.shape h₂ h₀ h₁ w.val S hS.2.1
            w.property hdiv).val a₀ a₁)).representation)

/-- Both segments of the datum have the rank of `ρ`. -/
theorem segment_rank_eq {ρ : CuspidalDatum.{uV, uF} T} {a₀ a₁ : ℝ} {n : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist a₀)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist a₁) :
    ∀ j, (d.segments j).rank = ρ.rank := by
  rintro ⟨j, hj⟩
  have hj2 : j = 0 ∨ j = 1 := by omega
  rcases hj2 with rfl | rfl
  · have h := congrArg CuspidalDatum.rank hb₀
    exact h
  · have h := congrArg CuspidalDatum.rank hb₁
    exact h

/-- The size of block `k` of `d.shape` is the length times the rank of its segment. -/
theorem shape_size_cast {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2)
    (k : Fin 2) :
    d.shape.size (Fin.cast h₂.symm k) =
      (d.segments ⟨k.val, by omega⟩).length * (d.segments ⟨k.val, by omega⟩).rank :=
  rfl

/-- Zelevinsky 1980, 1.6 and 3.1 for two segment socles, from the surviving
piece computation. -/
theorem twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv
    (h : SurvivingPieceEquiv.{uF, uV} F T) :
    TwoSegmentSocleShuffleJacquet.{uF, uV, uW} F T := by
  intro ρ A a₀ a₁ m₀ m₁ d h₂ hA hsoc hb₀ hl₀ hb₁ hl₁
  have hrank := segment_rank_eq F T d h₂ hb₀ hb₁
  have h₀ : d.shape.size (Fin.cast h₂.symm 0) = m₀ * ρ.rank := by
    rw [shape_size_cast F T d h₂ 0]
    exact (congrArg₂ (· * ·) hl₀ (hrank _))
  have h₁ : d.shape.size (Fin.cast h₂.symm 1) = m₁ * ρ.rank := by
    rw [shape_size_cast F T d h₂ 1]
    exact (congrArg₂ (· * ·) hl₁ (hrank _))
  exact shuffleJacquet_of_pieces.{uF, uV, uW} F T ρ A a₀ a₁ m₀ m₁ d h₂ hsoc hrank h₀ h₁
    (h ρ A a₀ a₁ m₀ m₁ d h₂ hA hsoc hb₀ hl₀ hb₁ hl₁ h₀ h₁)

end Langlands.Classification.TwoSegmentShuffle
