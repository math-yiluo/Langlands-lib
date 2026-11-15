import Langlands.Representation.Classification.LeftCuspidalDerivative.PieceCombinatorics
import Langlands.Representation.Classification.LeftCuspidalDerivative.PieceStructure
import Langlands.Representation.Classification.BinaryGeometricPieceConstituentsStatement
import Langlands.Representation.Classification.SegmentQuotientJacquetSingleBlock
import Langlands.Representation.Classification.SegmentSocleDerivativesProof
import Langlands.Representation.Induction.SingleBlock

/-!
# First-block constituents of the geometric pieces of a binary product

This file proves `BinaryGeometricPieces.BinaryGeometricPieceConstituents`. For two two-block
shapes `B` and `C`, an irreducible subquotient `ρ` of the first block of a geometric piece of
`r_C(Y₀ × Y₁)` is described by `exists_factors_of_isSubquotient_geometricPiece`: it is a
subquotient of the normalized induction along the first refined block `R j₀` of transported
factors of an irreducible family `X`. The first block of `C` has one or two inner blocks, each
coming from the first inner block of a block of `B` (`PieceCombinatorics`):

* one inner block coming from `Y₀`: then `w = 1`, and `ρ` is a first-block constituent of `Y₀`;
* one inner block coming from `Y₁`: `ρ` is a first-block constituent of `Y₁`;
* two inner blocks: they come from `Y₀` and `Y₁` in this order, and `ρ` is a subquotient of
  the normalized product of the two factors.

A factor sitting in the first inner block of a block `i` of `B` is a first-block Jacquet
constituent of `Y i`, since each block of `B` has at most two inner blocks.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport BinaryGeometricPieces

universe uF uV

section Helpers

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Casts

/-- Rank transports compose. -/
theorem castRank_trans {r s t : ℕ} (h₁ : r = s) (h₂ : s = t)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    T.castRank h₂ (T.castRank h₁ A) = T.castRank (h₁.trans h₂) A := by
  subst h₁
  subst h₂
  rfl

/-- A rank transport along `r = r` is the identity. -/
theorem castRank_self {r : ℕ} (h : r = r)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    T.castRank h A = A :=
  rfl

/-- Rank transports of a family at equal indices agree. -/
theorem castRank_family_eq {ι : Type*} {f : ι → ℕ}
    (X : letI := T.topology; ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (f k) F.Carrier))
    {k k' : ι} (hk : k = k') {m : ℕ} (h : f k = m) (h' : f k' = m) :
    T.castRank h (X k) = T.castRank h' (X k') := by
  subst hk
  rfl

/-- The rank-transported factor of a nested block is a rank transport. -/
theorem flattenedBlockFactor_eq {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (X : letI := T.topology
      ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier))
    (i : Fin B.length) (j : Fin (S i).length) :
    Parabolic.flattenedBlockFactor T B S X i j =
      T.castRank (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩)
        (X (B.flattenBlockEquiv S ⟨i, j⟩)) :=
  rfl

/-- The regrouped tensor of a block is the external tensor product of its factors. -/
theorem flattenedBlockTensor_eq {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (X : letI := T.topology
      ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier))
    (i : Fin B.length) :
    letI := T.topology
    Parabolic.flattenedBlockTensor T B S X i =
      FiniteTensor.externalSmoothObject (Parabolic.flattenedBlockFactor T B S X i) :=
  rfl

/-- The representation of the regrouped tensor of a block. -/
theorem flattenedBlockTensor_representation {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (X : letI := T.topology
      ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier))
    (i : Fin B.length) :
    letI := T.topology
    (Parabolic.flattenedBlockTensor T B S X i).representation =
      FiniteTensor.external
        (fun j => (Parabolic.flattenedBlockFactor T B S X i j).representation) :=
  rfl

/-- A factor of the transported family in an inner block `q` of `R` is the rank transport
of the factor of `X` in the source inner block of `q`. -/
theorem flattenedBlockFactor_transport {n : ℕ} {B C : BlockShape n}
    {w : Equiv.Perm (Fin n)} {S : BlockRefinement B} {R : BlockRefinement C}
    (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S) (C.flatten R) w)
    (X : letI := T.topology
      ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier))
    (q : (j : Fin C.length) × Fin (R j).length) :
    Parabolic.flattenedBlockFactor T C R
        (fun k => T.castRank (size_blockEquiv_symm hw k) (X ((blockEquiv hw).symm k)))
        q.1 q.2 =
      T.castRank (size_sourceBlock hw q)
        (Parabolic.flattenedBlockFactor T B S X (sourceBlock hw q).1 (sourceBlock hw q).2) := by
  rw [flattenedBlockFactor_eq, flattenedBlockFactor_eq, castRank_trans, castRank_trans]
  exact castRank_family_eq T X (flattenBlockEquiv_sourceBlock hw q).symm _ _

end Casts

section Shapes

/-- A two-block shape is a binary shape. -/
theorem exists_eq_ofPair {m : ℕ} (D : BlockShape m) (hD : D.length = 2) :
    ∃ (a k : ℕ) (ha : 0 < a) (hk : 0 < k) (h : a + k = m), D = BlockShape.ofPair a k ha hk h := by
  obtain ⟨l, s, hp, he⟩ := D
  dsimp only at hD
  subst hD
  refine ⟨s 0, s 1, hp 0, hp 1, by simpa [Fin.sum_univ_two] using he, ?_⟩
  refine TotalConjugatingCount.shape_ext rfl fun i => ?_
  fin_cases i <;> rfl

/-- The two sizes of a two-block shape add up to its rank. -/
theorem size_add_size_of_length_eq_two {m : ℕ} (D : BlockShape m) (hD : D.length = 2) :
    D.size ⟨0, by omega⟩ + D.size ⟨1, by omega⟩ = m := by
  obtain ⟨l, s, hp, he⟩ := D
  dsimp only at hD ⊢
  subst hD
  simpa [Fin.sum_univ_two] using he

/-- A block shape of positive rank has a block. -/
theorem length_pos_of_pos {m : ℕ} (D : BlockShape m) (hm : 0 < m) : 0 < D.length := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have he := D.sum_eq
  have : IsEmpty (Fin D.length) := by
    rw [h0]
    infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty] at he
  omega

end Shapes

section Constituents

/-- A first-block constituent passes to subquotients. -/
theorem isFirstBlockConstituent_of_isSubquotient {m a : ℕ}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    {ρ ρ' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h : IsFirstBlockConstituent.{uF, uV} F T Y ρ')
    (h' : letI := T.topology
      WeylBranchPieces.IsSubquotient ρ'.representation ρ.representation) :
    IsFirstBlockConstituent.{uF, uV} F T Y ρ := by
  rcases h with ⟨hm, hY⟩ | ⟨k, ha, hk, hak, hY⟩
  · exact Or.inl ⟨hm, hY.trans h'⟩
  · exact Or.inr ⟨k, ha, hk, hak, hY.trans h'⟩

/-- A first-block constituent passes to rank transports. -/
theorem isFirstBlockConstituent_castRank {m a a' : ℕ}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    {ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h : a = a') (hρ : IsFirstBlockConstituent.{uF, uV} F T Y ρ) :
    IsFirstBlockConstituent.{uF, uV} F T Y (T.castRank h ρ) := by
  subst h
  exact hρ

/-- **First inner blocks.** Let `D` be a block shape of `GL_m` with at most two blocks and `Z`
an irreducible family on its blocks whose external tensor product is a subquotient of the
normalized Jacquet module of `Y` along `D`. Then the factor of `Z` in the first block is a
first-block Jacquet constituent of `Y`. -/
theorem isFirstBlockConstituent_of_isSubquotient_jacquet {m : ℕ}
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (D : BlockShape m) (hD : D.length ≤ 2)
    (Z : letI := T.topology
      ∀ j : Fin D.length, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (D.size j) F.Carrier))
    (hZ : letI := T.topology; ∀ j, (Z j).IsIrreducible)
    (h : letI := T.topology
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject Z)
        ((T.normalizedJacquetFunctor D).obj Y))
    (j : Fin D.length) (hj : (j : ℕ) = 0) :
    IsFirstBlockConstituent.{uF, uV} F T Y (Z j) := by
  let := T.topology
  have h0 : WeylBranchPieces.IsSubquotient (T.normalizedJacquet D Y.representation)
      (FiniteTensor.external (fun j => (Z j).representation)) :=
    SmoothRep.isSubquotient_iff_representation.mp h
  have hV : ∀ j, Nontrivial (Z j) := fun j =>
    SegmentSocleDerivativesProof.nontrivial_of_isIrreducible (hZ j)
  have h1 : WeylBranchPieces.IsSubquotient
      ((T.normalizedJacquet D Y.representation).comp
        (MonoidHom.mulSingle (fun i => GeneralLinear (D.size i) F.Carrier) j))
      (Z j).representation :=
    (h0.comp _).trans (isSubquotient_external_comp_mulSingle _ hV j)
  have hpos : 0 < D.length := Fin.pos j
  rcases (show D.length = 1 ∨ D.length = 2 by omega) with hl | hl
  · -- One block: the Jacquet module is the rank-transported representation.
    refine Or.inl ⟨(D.singleBlock_size hl j).symm, ?_⟩
    have e := T.singleBlockNormalizedJacquetTensorEquiv D hl Y
    have h2 := WeylBranchPieces.IsSubquotient.of_equiv_left
      (FiniteTensorFiltration.compCongr e.symm
        (MonoidHom.mulSingle (fun i => GeneralLinear (D.size i) F.Carrier) j)) h1
    exact isSubquotient_factor_of_external_comp_mulSingle
      (H := fun i => GeneralLinear (D.size i) F.Carrier)
      (fun i => (T.castRank (D.singleBlock_size hl i).symm Y).representation) j
      (Z j).representation (hZ j) h2
  · -- Two blocks: the shape is a binary shape.
    obtain ⟨a', k', ha', hk', hak, rfl⟩ := exists_eq_ofPair D hl
    obtain rfl : j = ⟨0, Nat.zero_lt_two⟩ := Fin.ext hj
    exact Or.inr ⟨k', ha', hk', hak, h1⟩

end Constituents

section Induction

/-- **One inner block.** A subquotient of the normalized induction along a one-block shape is
a subquotient of the rank-transported unique factor. -/
theorem isSubquotient_castRank_of_singleBlock {a : ℕ} (D : BlockShape a) (hD : D.length = 1)
    (Z : letI := T.topology
      ∀ j : Fin D.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size j) F.Carrier))
    (i : Fin D.length) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear a F.Carrier) W)
    (h : letI := T.topology
      WeylBranchPieces.IsSubquotient
        (T.normalizedParabolicInduced D (FiniteTensor.externalSmoothObject Z).representation)
        ρ) :
    letI := T.topology
    WeylBranchPieces.IsSubquotient (T.castRank (D.singleBlock_size hD i) (Z i)).representation
      ρ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup a
  have e1 := T.singleBlockNormalizedProductEquiv D hD (fun j => (Z j).representation)
    (fun j => (Z j).isSmooth) i
  have e2 := T.castRankEquiv (D.singleBlock_size hD i) (Z i)
  have h' : WeylBranchPieces.IsSubquotient
      (T.normalizedParabolicInduced D (FiniteTensor.external (fun j => (Z j).representation))) ρ :=
    h
  exact WeylBranchPieces.IsSubquotient.of_equiv_left (e1.trans e2).symm h'

/-- **Two inner blocks.** A subquotient of the normalized induction along a two-block shape is
a subquotient of the (rank-transported) binary normalized product of the two factors. -/
theorem isSubquotient_binaryProduct_of_twoBlock {a : ℕ} (D : BlockShape a) (hD : D.length = 2)
    (Z : letI := T.topology
      ∀ j : Fin D.length, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (D.size j) F.Carrier))
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (h : letI := T.topology
      WeylBranchPieces.IsSubquotient
        (T.normalizedParabolicInduced D (FiniteTensor.externalSmoothObject Z).representation)
        ρ.representation)
    (hsum : D.size ⟨0, by omega⟩ + D.size ⟨1, by omega⟩ = a) :
    letI := T.topology
    SmoothRep.IsSubquotient ρ (T.castRank hsum
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} (D.size ⟨0, by omega⟩)
        (D.size ⟨1, by omega⟩)).obj (Z ⟨0, by omega⟩, Z ⟨1, by omega⟩))) := by
  let := T.topology
  replace h : WeylBranchPieces.IsSubquotient
      (T.normalizedParabolicInduced D (FiniteTensor.external (fun j => (Z j).representation)))
      ρ.representation := h
  obtain ⟨a', k', ha', hk', hak, rfl⟩ := exists_eq_ofPair D hD
  subst hak
  obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T ha' hk'
    (Z ⟨0, Nat.zero_lt_two⟩) (Z ⟨1, Nat.one_lt_two⟩)
  have hZ : (twoBlockFactors ha' hk' (Z ⟨0, Nat.zero_lt_two⟩) (Z ⟨1, Nat.one_lt_two⟩) :
      ∀ j : Fin (BlockShape.ofPair a' k' ha' hk' rfl).length,
        SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear ((BlockShape.ofPair a' k' ha' hk' rfl).size j) F.Carrier)) = Z := by
    funext i
    rcases i with ⟨_ | _ | i, hi⟩
    · rfl
    · rfl
    · simp only at hi
      omega
  rw [hZ] at e
  exact SmoothRep.isSubquotient_iff_representation.mpr
    (WeylBranchPieces.IsSubquotient.of_equiv_left (SmoothRep.equivOfIso e) h)

end Induction

end Helpers

section Main

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Each factor in the first block of `C` of the transported family is a first-block
constituent of the block of `B` it comes from. -/
theorem isFirstBlockConstituent_flattenedBlockFactor {n : ℕ} {B C : BlockShape n}
    {w : Equiv.Perm (Fin n)} (hmin : IsMinimalRepresentative B C w)
    {S : BlockRefinement B} {R : BlockRefinement C}
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S) (C.flatten R) w) (hC : C.length = 2)
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (X : letI := T.topology
      ∀ k, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier))
    (hXi : letI := T.topology; ∀ k, (X k).IsIrreducible)
    (hsrc : letI := T.topology
      ∀ i, SmoothRep.IsSubquotient (Parabolic.flattenedBlockTensor T B S X i)
        ((T.normalizedJacquetFunctor (S i)).obj (Y i)))
    (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0) (l : Fin (R j₀).length) :
    IsFirstBlockConstituent.{uF, uV} F T (Y (sourceBlock hw ⟨j₀, l⟩).1)
      (Parabolic.flattenedBlockFactor T C R
        (fun k => T.castRank (size_blockEquiv_symm hw k) (X ((blockEquiv hw).symm k))) j₀ l) := by
  let := T.topology
  let q : (j : Fin C.length) × Fin (R j).length := ⟨j₀, l⟩
  have hsrc0 : ((sourceBlock hw q).2 : ℕ) = 0 := sourceBlock_snd_eq_zero hmin hS hw q hj₀
  have hlen : (S (sourceBlock hw q).1).length ≤ 2 :=
    (refinement_length_le hmin hS (sourceBlock hw q).1).trans hC.le
  have hZ : ∀ j, (Parabolic.flattenedBlockFactor T B S X (sourceBlock hw q).1 j).IsIrreducible :=
    fun j => T.isIrreducible_castRank _ _ (hXi _)
  have hs := hsrc (sourceBlock hw q).1
  rw [flattenedBlockTensor_eq] at hs
  have h1 := isFirstBlockConstituent_of_isSubquotient_jacquet T (Y (sourceBlock hw q).1)
    (S (sourceBlock hw q).1) hlen (Parabolic.flattenedBlockFactor T B S X (sourceBlock hw q).1)
    hZ hs (sourceBlock hw q).2 hsrc0
  have h2 := isFirstBlockConstituent_castRank T (size_sourceBlock hw q) h1
  rw [← flattenedBlockFactor_transport T hw X q] at h2
  exact h2

/-- **The case analysis**, for an abstract conjugation `hw` and a family `X` as produced by
`exists_factors_of_isSubquotient_geometricPiece`. -/
theorem pieceConstituents_of_factors {n : ℕ} {B C : BlockShape n}
    (hB : B.length = 2) (hC : C.length = 2)
    {w : Equiv.Perm (Fin n)} (hmin : IsMinimalRepresentative B C w)
    {S : BlockRefinement B} {R : BlockRefinement C}
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hw : ConjugatesLevi (F := F.Carrier) (B.flatten S) (C.flatten R) w)
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0)
    (ρ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size j₀) F.Carrier))
    (X : letI := T.topology
      ∀ k, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((B.flatten S).size k) F.Carrier))
    (hXi : letI := T.topology; ∀ k, (X k).IsIrreducible)
    (hsrc : letI := T.topology
      ∀ i, SmoothRep.IsSubquotient (Parabolic.flattenedBlockTensor T B S X i)
        ((T.normalizedJacquetFunctor (S i)).obj (Y i)))
    (htgt : letI := T.topology
      WeylBranchPieces.IsSubquotient
        (T.normalizedParabolicInduced (R j₀)
          (Parabolic.flattenedBlockTensor T C R
            (fun k => T.castRank (size_blockEquiv_symm hw k) (X ((blockEquiv hw).symm k)))
            j₀).representation)
        ρ.representation) :
    (w = 1 ∧ IsFirstBlockConstituent.{uF, uV} F T (Y ⟨0, by omega⟩) ρ) ∨
      IsFirstBlockConstituent.{uF, uV} F T (Y ⟨1, by omega⟩) ρ ∨
      IsMixedConstituent.{uF, uV} F T (Y ⟨0, by omega⟩) (Y ⟨1, by omega⟩) ρ := by
  let := T.topology
  let X' : ∀ k : Fin (C.flatten R).length,
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((C.flatten R).size k) F.Carrier) :=
    fun k => T.castRank (size_blockEquiv_symm hw k) (X ((blockEquiv hw).symm k))
  rw [flattenedBlockTensor_eq] at htgt
  -- The factors in the first block of `C` are irreducible.
  have hirr : ∀ l, (Parabolic.flattenedBlockFactor T C R X' j₀ l).IsIrreducible := fun l =>
    T.isIrreducible_castRank _ _ (T.isIrreducible_castRank _ _ (hXi _))
  -- Each factor in the first block of `C` is a first-block constituent of its source.
  have hFF := isFirstBlockConstituent_flattenedBlockFactor.{uF, uV} T hmin hS hw hC Y X hXi hsrc
    j₀ hj₀
  have hlen0 : (R j₀).length ≤ 2 := (length_le_of_sourceBlock hmin hS hw j₀ hj₀).trans hB.le
  have hpos0 : 0 < (R j₀).length := length_pos_of_pos (R j₀) (C.positive j₀)
  rcases (show (R j₀).length = 1 ∨ (R j₀).length = 2 by omega) with hl | hl
  · -- One inner block: `ρ` is a constituent of the factor coming from a single block of `B`.
    let l₀ : Fin (R j₀).length := ⟨0, by omega⟩
    have hρ1 := isSubquotient_castRank_of_singleBlock T (R j₀) hl
      (Parabolic.flattenedBlockFactor T C R X' j₀) l₀ ρ.representation htgt
    have hF := isFirstBlockConstituent_of_isSubquotient T
      (isFirstBlockConstituent_castRank T ((R j₀).singleBlock_size hl l₀) (hFF l₀)) hρ1
    have hlt := (sourceBlock hw ⟨j₀, l₀⟩).1.isLt
    rcases (show ((sourceBlock hw ⟨j₀, l₀⟩).1 : ℕ) = 0 ∨
        ((sourceBlock hw ⟨j₀, l₀⟩).1 : ℕ) = 1 by omega) with hs | hs
    · have he : (sourceBlock hw ⟨j₀, l₀⟩).1 = ⟨0, by omega⟩ := Fin.ext hs
      rw [he] at hF
      exact Or.inl ⟨eq_one_of_sourceBlock hmin hS hw hC j₀ hj₀ hl hs, hF⟩
    · have he : (sourceBlock hw ⟨j₀, l₀⟩).1 = ⟨1, by omega⟩ := Fin.ext hs
      rw [he] at hF
      exact Or.inr (Or.inl hF)
  · -- Two inner blocks: they come from the two blocks of `B` in order.
    let l₀ : Fin (R j₀).length := ⟨0, by omega⟩
    let l₁ : Fin (R j₀).length := ⟨1, by omega⟩
    have hF0 := hFF l₀
    have hF1 := hFF l₁
    have he0 : (sourceBlock hw ⟨j₀, l₀⟩).1 = ⟨0, by omega⟩ :=
      Fin.ext (sourceBlock_fst_val_of_length_two hmin hS hw hB j₀ hj₀ hl l₀)
    have he1 : (sourceBlock hw ⟨j₀, l₁⟩).1 = ⟨1, by omega⟩ :=
      Fin.ext (sourceBlock_fst_val_of_length_two hmin hS hw hB j₀ hj₀ hl l₁)
    rw [he0] at hF0
    rw [he1] at hF1
    have hsum := size_add_size_of_length_eq_two (R j₀) hl
    have hmix := isSubquotient_binaryProduct_of_twoBlock.{uF, uV} T (R j₀) hl
      (Parabolic.flattenedBlockFactor T C R X' j₀) ρ htgt hsum
    exact Or.inr (Or.inr ⟨(R j₀).size l₀, (R j₀).size l₁, (R j₀).positive l₀,
      (R j₀).positive l₁, hsum, _, _, hirr l₀, hirr l₁, hF0, hF1, hmix⟩)

/-- **Constituents of the first block of a geometric piece, for two two-block shapes.** -/
theorem pieceConstituents_of_twoBlocks {n : ℕ} (hn : 0 < n) (B C : BlockShape n)
    (hB : B.length = 2) (hC : C.length = 2)
    (w : Equiv.Perm (Fin n)) (hmin : IsMinimalRepresentative B C w)
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hY : letI := T.topology; ∀ i, (Y i).HasFiniteLength)
    (j₀ : Fin C.length) (hj₀ : (j₀ : ℕ) = 0)
    (ρ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size j₀) F.Carrier))
    (hρ : letI := T.topology; ρ.IsIrreducible)
    (h : letI := T.topology
      WeylBranchPieces.IsSubquotient
        (((geometricPieceFunctor.{uF, max uF uV} T B C w S R hS hR).obj
            (FiniteTensor.externalSmoothObject Y)).ρ.comp
          (MonoidHom.mulSingle (fun i => GeneralLinear (C.size i) F.Carrier) j₀))
        ρ.representation) :
    (w = 1 ∧ IsFirstBlockConstituent.{uF, uV} F T (Y ⟨0, by omega⟩) ρ) ∨
      IsFirstBlockConstituent.{uF, uV} F T (Y ⟨1, by omega⟩) ρ ∨
      IsMixedConstituent.{uF, uV} F T (Y ⟨0, by omega⟩) (Y ⟨1, by omega⟩) ρ := by
  let := T.topology
  obtain ⟨X, hXi, -, hsrc, htgt⟩ :=
    exists_factors_of_isSubquotient_geometricPiece.{uF, uV} T hn B C w hmin S R hS hR Y hY j₀ ρ hρ h
  exact pieceConstituents_of_factors.{uF, uV} T hB hC hmin hS
    (conjugatesLevi_flattened_intersections F.Carrier B C w S R hS hR) Y j₀ hj₀ ρ X hXi hsrc htgt

/-- **The statement `BinaryGeometricPieceConstituents`.** -/
theorem binaryGeometricPieceConstituents : BinaryGeometricPieceConstituents.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro m₁ m₂ h₁ h₂ a b ha hb h w S R hS hR Y₁ Y₂ ρ hY₁ hY₂ hρ hsub
  have hY : ∀ i, (twoBlockFactors h₁ h₂ Y₁ Y₂ i).HasFiniteLength := by
    rintro ⟨_ | _ | i, hi⟩
    · exact hY₁
    · exact hY₂
    · exact absurd hi (by simp)
  exact pieceConstituents_of_twoBlocks.{uF, uV} T (by omega)
    (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl) (BlockShape.ofPair a b ha hb h) rfl rfl w.1 w.2 S R
    hS.2.1 hR.2.1 (twoBlockFactors h₁ h₂ Y₁ Y₂) hY (0 : Fin 2) rfl ρ hρ
    (by with_reducible exact hsub)

end Main

end Langlands.Classification.LeftCuspidalDerivative
