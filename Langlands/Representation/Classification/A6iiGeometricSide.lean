import Langlands.Representation.Classification.A6iiSilbergerSide
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetFiniteLengthProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Classification.SegmentProductConcatenation

/-!
# The geometric side of the head comparison

Let `π_i` be irreducible quotients of `λ(d'_i)` whose segments are ordered by
decreasing exponents, with irreducible normalized product `Π`. The cuspidal tensor
`⊠ ν^j A` in the merged order of all segments occurs in the opposite Jacquet
module of `Π`: the merged order keeps the order of the supercuspidal blocks coming
from each factor, so it is a minimal reordering and the geometric piece applies.
-/

noncomputable section

namespace Langlands.Classification.A6ii

open CategoryTheory GeneralLinear Geometric WeylBranchPieces PadicField.TopologicalData

universe uF uV

section Labels

variable {α : Type*} (len : α → ℕ)

/-- Pairs of a label and a position below its length. -/
def sigmaFinSubtype : ((q : α) × Fin (len q)) ≃ {x : α × ℕ // x.2 < len x.1} where
  toFun x := ⟨(x.1, x.2.val), x.2.isLt⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Labels

/-- The homomorphism of an isomorphism of smooth representations is surjective. -/
theorem iso_hom_surjective {R G : Type*} [CommRing R] [Group G] [TopologicalSpace G]
    {X Y : SmoothRep.{_, _, uV} R G} (e : X ≅ Y) : Function.Surjective (SmoothRep.hom e.hom) :=
  fun y => ⟨SmoothRep.hom e.inv y, by
    change SmoothRep.hom (e.inv ≫ e.hom) y = y
    rw [Iso.inv_hom_id]
    rfl⟩

variable {p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 2000000 in
/-- The geometric side: the merged cuspidal tensor occurs in the opposite Jacquet
module of the irreducible product. -/
theorem geometricSide (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ} (hn : 0 < n)
    (B : BlockShape n) (d' : ∀ i, T.SegmentProductDatum.{max uF uV, uF} (B.size i))
    (A' : letI := T.topology
      ∀ q : (i : Fin B.length) × Fin (d' i).length,
        SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ((d' q.1).segments q.2).rank))
    (hA' : letI := T.topology
      ∀ q : (i : Fin B.length) × Fin (d' i).length,
        IsIrreducibleQuotient
          (T.segmentInduced (A' q).obj ((d' q.1).segments q.2).length
            ((d' q.1).segments q.2).rank_pos).representation
          ((d' q.1).blocks q.2).representation)
    (π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hπi : letI := T.topology; ∀ i, Representation.IsIrreducible (π i).representation)
    (hπa : letI := T.topology; ∀ i, IsAdmissible (π i).representation)
    (qd : letI := T.topology; ∀ i, (d' i).induced ⟶ π i)
    (hqd : letI := T.topology; ∀ i, Function.Surjective (SmoothRep.hom (qd i)))
    (hPi : letI := T.topology
      Representation.IsIrreducible ((T.normalizedProductInductionFunctor B).obj π).representation)
    {ex : Fin (SegmentProductDatum.concatenate B d').length → ℝ}
    (hanti : ∀ i, Antitone (fun s : Fin (d' i).length => ex (finSigmaFinEquiv ⟨i, s⟩)))
    (m : MergeGrouping n
      (fun ℓ => ((SegmentProductDatum.concatenate B d').segments ℓ).degree) ex) :
    letI := T.topology
    ∃ k, 0 < k ∧ HasJordanHolderMultiplicity
      (CuspidalJacquetMultiplicity.oppositeJacquet T
        (fineShape (SegmentProductDatum.concatenate B d') m)
        ((T.normalizedProductInductionFunctor B).obj π).obj)
      (fineAtoms F T (SegmentProductDatum.concatenate B d') m
        (fun l => A' (finSigmaFinEquiv.symm l))) k := by
  let := T.topology
  let c := SegmentProductDatum.concatenate B d'
  let Λ₀ := (i : Fin B.length) × Fin (d' i).length
  let len : Λ₀ → ℕ := fun q => ((d' q.1).segments q.2).length
  let fSF : Λ₀ ≃ Fin c.length := finSigmaFinEquiv
  -- the refinement of every factor into its supercuspidal blocks
  let U : ∀ i, BlockRefinement (d' i).shape := fun i s =>
    BlockShape.uniform ((d' i).segments s).length ((d' i).segments s).rank
      ((d' i).segments s).rank_pos
  let S' : BlockRefinement B := fun i => (d' i).shape.flatten (U i)
  let P := B.flatten S'
  let fP := B.flattenBlockEquiv S'
  let fU := fun i => (d' i).shape.flattenBlockEquiv (U i)
  let Y : ∀ q : (i : Fin B.length) × Fin (S' i).length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := (S' q.1).size q.2) :=
    fun q => twistSC F T ((((fU q.1).symm q.2).2 : ℕ) : ℝ) (A' ⟨q.1, ((fU q.1).symm q.2).1⟩)
  -- every factor is a quotient of the induction of its supercuspidal blocks
  have hqs := fun q : Λ₀ => (hA' q).2
  choose qs hqs using hqs
  have hqπ : ∀ i, ∃ f : (T.normalizedProductInductionFunctor (S' i)).obj
      (fun j => (Y ⟨i, j⟩).obj) ⟶ π i, Function.Surjective (SmoothRep.hom f) := by
    intro i
    obtain ⟨E1⟩ := nonempty_flatten_iso.{uF, max uF uV} F T (d' i).shape (U i)
      (fun s t => (twistSC F T ((t : ℕ) : ℝ) (A' ⟨i, s⟩)).obj)
    let f2 : (T.normalizedProductInductionFunctor (d' i).shape).obj
        (fun s => T.segmentInduced (A' ⟨i, s⟩).obj ((d' i).segments s).length
          ((d' i).segments s).rank_pos) ⟶ (d' i).induced :=
      (T.normalizedProductInductionFunctor (d' i).shape).map
        (fun s => SmoothRep.ofHom (qs ⟨i, s⟩))
    have h2 : Function.Surjective (SmoothRep.hom f2) :=
      productMap_surjective F T (d' i).shape (fun s => SmoothRep.ofHom (qs ⟨i, s⟩))
        (fun s => hqs ⟨i, s⟩)
    refine ⟨E1.hom ≫ f2 ≫ qd i, ?_⟩
    exact (hqd i).comp (h2.comp (iso_hom_surjective E1))
  choose qπ hqπ using hqπ
  -- the labels of the blocks of both fine shapes
  let D := m.shape.flatten (mergedRefinement c m)
  let R := segmentRefinement c m
  let fR := D.flattenBlockEquiv R
  let E₀ : Fin D.length ≃ Λ₀ := (mergedEquiv c m).trans fSF.symm
  let toSub : ((i : Fin B.length) × (s : Fin (d' i).length) × Fin (len ⟨i, s⟩)) ≃
      {x : Λ₀ × ℕ // x.2 < len x.1} :=
    (Equiv.sigmaAssoc (fun i (s : Fin (d' i).length) => Fin (len ⟨i, s⟩))).symm.trans
      (sigmaFinSubtype len)
  let labP : Fin P.length ≃ {x : Λ₀ × ℕ // x.2 < len x.1} :=
    (fP.symm.trans (Equiv.sigmaCongrRight fun i => (fU i).symm)).trans toSub
  let toSub₀ : ((a : Fin D.length) × Fin (R a).length) ≃ {x : Λ₀ × ℕ // x.2 < len x.1} :=
    (Equiv.sigmaCongrLeft (β := fun q : Λ₀ => Fin (len q)) E₀).trans (sigmaFinSubtype len)
  let lab₀ : Fin (fineShape c m).length ≃ {x : Λ₀ × ℕ // x.2 < len x.1} := fR.symm.trans toSub₀
  have hl : P.length = (fineShape c m).length := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (labP.trans lab₀.symm)
  let e : Equiv.Perm (Fin P.length) := (finCongr hl).trans (lab₀.trans labP.symm)
  have labP_val : ∀ i (s : Fin (d' i).shape.length) (t : Fin (U i s).length),
      (labP (fP ⟨i, fU i ⟨s, t⟩⟩)).val = (⟨i, s⟩, t.val) := by
    intro i s t
    change (toSub ((Equiv.sigmaCongrRight fun i => (fU i).symm)
      (fP.symm (fP ⟨i, fU i ⟨s, t⟩⟩)))).val = _
    rw [Equiv.symm_apply_apply, Equiv.sigmaCongrRight_apply, Equiv.symm_apply_apply]
    rfl
  have lab₀_val : ∀ (a : Fin D.length) (t : Fin (R a).length),
      (lab₀ (fR ⟨a, t⟩)).val = (E₀ a, t.val) := by
    intro a t
    change (toSub₀ (fR.symm (fR ⟨a, t⟩))).val = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hlabe : ∀ k, labP k = lab₀ (Fin.cast hl (e.symm k)) := by
    intro k
    have h : labP.symm (lab₀ (Fin.cast hl (e.symm k))) = k := e.apply_symm_apply k
    calc labP k = labP (labP.symm (lab₀ (Fin.cast hl (e.symm k)))) := by rw [h]
      _ = _ := labP.apply_symm_apply _
  -- the reordering keeps the order inside every factor
  have hstab : ∀ k k', (fP.symm k).1 = (fP.symm k').1 → k < k' → e.symm k < e.symm k' := by
    intro k k' hkk hlt
    suffices hcast : Fin.cast hl (e.symm k) < Fin.cast hl (e.symm k') by
      simpa only [Fin.lt_def, Fin.val_cast] using hcast
    obtain ⟨⟨i, j⟩, rfl⟩ := fP.surjective k
    obtain ⟨⟨i', j'⟩, rfl⟩ := fP.surjective k'
    simp only [Equiv.symm_apply_apply] at hkk
    subst hkk
    obtain ⟨⟨s, t⟩, rfl⟩ := (fU i).surjective j
    obtain ⟨⟨s', t'⟩, rfl⟩ := (fU i).surjective j'
    have hj : fU i ⟨s, t⟩ < fU i ⟨s', t'⟩ := by
      rcases (B.flattenBlockEquiv_lt_iff S' ⟨i, fU i ⟨s, t⟩⟩ ⟨i, fU i ⟨s', t'⟩⟩).mp hlt with
        h | ⟨-, h⟩
      · exact absurd h (lt_irrefl _)
      · exact h
    have hst := ((d' i).shape.flattenBlockEquiv_lt_iff (U i) ⟨s, t⟩ ⟨s', t'⟩).mp hj
    obtain ⟨⟨a, τ₁⟩, hK⟩ := fR.surjective (Fin.cast hl (e.symm (fP ⟨i, fU i ⟨s, t⟩⟩)))
    obtain ⟨⟨a', τ₂⟩, hK'⟩ := fR.surjective (Fin.cast hl (e.symm (fP ⟨i, fU i ⟨s', t'⟩⟩)))
    have v1 := congrArg Subtype.val (hlabe (fP ⟨i, fU i ⟨s, t⟩⟩))
    have v2 := congrArg Subtype.val (hlabe (fP ⟨i, fU i ⟨s', t'⟩⟩))
    rw [← hK, labP_val, lab₀_val] at v1
    rw [← hK', labP_val, lab₀_val] at v2
    obtain ⟨hq1, ht1⟩ := Prod.mk.inj v1
    obtain ⟨hq2, ht2⟩ := Prod.mk.inj v2
    rw [← hK, ← hK']
    apply (D.flattenBlockEquiv_lt_iff R ⟨a, τ₁⟩ ⟨a', τ₂⟩).mpr
    have ha : a = E₀.symm ⟨i, s⟩ := by rw [hq1, Equiv.symm_apply_apply]
    have ha' : a' = E₀.symm ⟨i, s'⟩ := by rw [hq2, Equiv.symm_apply_apply]
    rcases hst with hs | ⟨hs, ht⟩
    · left
      change a < a'
      rw [ha, ha']
      change (m.shape.flattenBlockEquiv (mergedRefinement c m))
          (m.label.symm (fSF ⟨i, s⟩)) <
        (m.shape.flattenBlockEquiv (mergedRefinement c m)) (m.label.symm (fSF ⟨i, s'⟩))
      apply m.lt_of_lt
      · rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact BlockShape.finSigmaFinEquiv_lt_of (Or.inr ⟨rfl, hs⟩)
      · rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hanti i hs.le
    · right
      change s = s' at hs
      subst hs
      refine ⟨ha.trans ha'.symm, ?_⟩
      change τ₁.val < τ₂.val
      rw [← ht1, ← ht2]
      exact ht
  have hmin := isMinimalRepresentative_permute_flatten B S' e hstab
  -- the geometric piece and its transport to the merged fine shape
  have hpiece := geometricPiece.{uF, max uF uV} T hn B S' Y π hπi hπa qπ hqπ e hmin
  have hC : P.permute e = fineShape c m := by
    refine BlockShape.ext_of_size (B₁ := P.permute e) hl ?_
    intro k
    change ((d' (labP (e k)).val.1.1).segments (labP (e k)).val.1.2).rank =
      ((d' (lab₀ (Fin.cast hl k)).val.1.1).segments (lab₀ (Fin.cast hl k)).val.1.2).rank
    have : labP (e k) = lab₀ (Fin.cast hl k) := labP.apply_symm_apply _
    rw [this]
  have hsub := isSubquotient_blockTensor_cast.{uF, max uF uV} T hC
    ((T.normalizedProductInductionFunctor B).obj π).obj
    (fun x : Λ₀ × ℕ => ((d' x.1.1).segments x.1.2).rank)
    (fun x => (twistSC F T ((x.2 : ℕ) : ℝ) (A' x.1)).obj)
    (fun k => (labP (e k)).val) (fun k => (lab₀ k).val) (fun k => rfl) (fun k => rfl)
    (fun k => congrArg Subtype.val (labP.apply_symm_apply _).symm) hpiece
  -- positivity of the count
  obtain ⟨hτi, -⟩ := CuspidalSupport.glCuspidalTensor.{max uF uV, uF} p F T n hn
    (fineShape c m) (fun k => twistSC F T ((((fR.symm k).2 : ℕ) : ℝ))
      (A' (fSF.symm (mergedLabel c m (fR.symm k).1))))
  have hPia : IsAdmissible ((T.normalizedProductInductionFunctor B).obj π).representation :=
    Parabolic.normalizedInductionAdmissibility F T B _
      (B.blockTensor fun i => (π i).representation)
      (FiniteTensor.isAdmissible_external _ hπa)
  have hfin := Parabolic.oppositeJacquetFiniteLength T (fineShape c m)
    ((T.normalizedProductInductionFunctor B).obj π).representation hPia
    (Parabolic.IrreducibleOppositeJacquetFiniteLength.finite_asModule_of_irreducible _ hPi)
  exact count_pos_of_isSubquotient hτi hfin hsub

end Langlands.Classification.A6ii
