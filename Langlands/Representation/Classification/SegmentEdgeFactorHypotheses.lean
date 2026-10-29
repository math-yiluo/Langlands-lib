import Langlands.Representation.Classification.SegmentEdgeJacquetStatement
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.Representation.Classification.SegmentQuotientJacquetSingleBlock
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Filtration.SubsingletonProof
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Induction.HeterogeneousPairs

/-!
# The factor hypotheses of the merged-slot Jacquet filtration

The statement `SegmentEdgeJacquetFiltration` has two hypotheses on the factors
`Y_j` of the merged shape `γ`: (H1) vanishing of their normalized Jacquet modules
along shapes with at least two blocks other than `S_j`, and (H2) the Jacquet
module along `S_j`. For uniform supercuspidal block factors `σ`, this module
proves both for the slot products `i_{S_j}(σ_{e(j,0)}, …)`, for their
subrepresentations and quotients, and, at the merged slot, transports Ze80
Proposition 1.11(b) from the standard shape `(r, r)` to the slot.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.SegmentEdge

open GeneralLinear Geometric CuspidalSupport CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

section Vanishing

/-- The image of a refined Levi in the ambient group is the Levi subgroup of
the flattened shape. -/
theorem refinedLevi_map_eq_flatten_leviSubgroup {K : Type*} [Field K] {n : ℕ}
    (D : BlockShape n) (S : BlockRefinement D) :
    (refinedLevi K D S).map (D.leviEmbedding K) = (D.flatten S).leviSubgroup K := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(flattenedLeviEquiv K D S).symm ⟨m, hm⟩,
      flattenedLeviEquiv_symm_embedding K D S ⟨m, hm⟩⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(flattenedLeviEquiv K D S m).val, (flattenedLeviEquiv K D S m).property,
      flattenedLeviEquiv_embedding K D S m⟩

/-- If the Levi of a shape `B` whose blocks all have the same size is conjugate
to the Levi of a refinement of a shape `D` with at least as many blocks as `B`,
then `D = B`. -/
theorem eq_of_conjugatesLevi_flatten {K : Type*} [Field K] {n : ℕ} {B D : BlockShape n}
    (hB : ∀ i i', B.size i = B.size i') (hlen : B.length ≤ D.length)
    (S : BlockRefinement D) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := K) B (D.flatten S) w) : D = B := by
  have hsum : B.length = ∑ i, (S i).length := TotalConjugatingCount.length_eq hw
  have hpos : ∀ i, 1 ≤ (S i).length := fun i =>
    (blockIndex (S i) ⟨0, D.positive i⟩).pos
  have hle : ∑ _i : Fin D.length, 1 ≤ ∑ i, (S i).length :=
    Finset.sum_le_sum fun i _ => hpos i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at hle
  have hDlen : D.length = B.length := by omega
  have hone : ∀ i, (S i).length = 1 := by
    have hsum' : ∑ _i : Fin D.length, 1 = ∑ i, (S i).length := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one]
      omega
    intro i
    exact ((Finset.sum_eq_sum_iff_of_le fun i _ => hpos i).mp hsum' i
      (Finset.mem_univ i)).symm
  have hflat : ∀ j i', (D.flatten S).size j = B.size i' := by
    intro j i'
    obtain ⟨i, rfl⟩ := TotalConjugatingCount.blockMap_surjective hw j
    rw [TotalConjugatingCount.size_blockMap hw i]
    exact hB i i'
  have hsize : ∀ i i', D.size i = B.size i' := by
    intro i i'
    have h0 : 0 < (S i).length := by rw [hone i]; exact Nat.one_pos
    rw [← (S i).singleBlock_size (hone i) ⟨0, h0⟩,
      ← D.flatten_size_flattenBlockEquiv S ⟨i, ⟨0, h0⟩⟩]
    exact hflat _ i'
  exact TotalConjugatingCount.shape_ext hDlen fun j => hsize j _

/-- For a shape `B` whose blocks all have the same size, no refinement of a
shape `D ≠ B` with at least as many blocks as `B` has a Levi conjugate to the
Levi of `B`. -/
theorem no_associated_refinement_of_size_eq {K : Type*} [Field K] {n : ℕ}
    {B : BlockShape n} (hB : ∀ i i', B.size i = B.size i') (D : BlockShape n)
    (hlen : B.length ≤ D.length) (hne : D ≠ B) :
    ¬ ∃ (S : BlockRefinement D) (w : Equiv.Perm (Fin n)),
      (B.leviSubgroup K).map (MulAut.conj (permutation n K w)).toMonoidHom =
        (refinedLevi K D S).map (D.leviEmbedding K) := by
  rintro ⟨S, w, h⟩
  rw [refinedLevi_map_eq_flatten_leviSubgroup] at h
  exact hne (eq_of_conjugatesLevi_flatten hB hlen S w h)

/-- The normalized Jacquet module along `C` of the normalized induction from `B`
of a quasicuspidal representation vanishes when no refinement of `C` has a Levi
conjugate to the Levi of `B`, given the geometric lemma for `(B, C)`. -/
theorem jacquet_induction_subsingleton_of_geometricLemma {n : ℕ} (B C : BlockShape n)
    (hgeo : GeometricLemmaTheorem.{uF, uV} T B C) :
    letI := T.topology
    ∀ ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B ρ.representation →
      (¬ ∃ (S : BlockRefinement C) (w : Equiv.Perm (Fin n)),
        (B.leviSubgroup F.Carrier).map
          (MulAut.conj (permutation n F.Carrier w)).toMonoidHom =
          (refinedLevi F.Carrier C S).map (C.leviEmbedding F.Carrier)) →
      Subsingleton ((T.normalizedJacquetFunctor C).obj
        ((T.normalizedParabolicInductionFunctor B).obj ρ)) := by
  let := T.topology
  intro ρ hρ hBC
  obtain ⟨S, R, hS, hR, m, e, order, s, hs⟩ := hgeo
  let enum := order.trans e
  let evaluated := objectFiltrationAt s ρ
  have zero (i : Fin m) : Subsingleton (evaluated.gradedRepresentation i) := by
    obtain ⟨iso⟩ := hs i
    have hP := geometricPieceFunctor_subsingleton_of_proper_source F T B C (enum i).val
      (S (enum i)) (R (enum i)) (hS (enum i)).2.1 (hR (enum i)).2.1 ρ hρ
      (source_refinement_proper_of_no_associated_refinement B C hBC (enum i).val
        (S (enum i)) (R (enum i)) (hS (enum i)) (hR (enum i)))
    exact @Function.Injective.subsingleton _ _ _
      (Representation.equivOfIso (iso.app ρ)).toLinearEquiv.injective hP
  exact objectRepFiltrationSubsingleton ℂ (C.Levi F.Carrier) _ m evaluated zero

/-- For a shape `B` whose blocks all have the same size and supercuspidal block
factors `A`, the normalized Jacquet module of `i_B(A)` along every shape
`D ≠ B` with at least as many blocks as `B` vanishes, given the geometric lemma
for `(B, D)`. -/
theorem induced_jacquet_subsingleton {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (hB : ∀ i i', B.size i = B.size i')
    (hgeo : ∀ D : BlockShape n, GeometricLemmaTheorem.{uF, uV} T B D) :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
      (D : BlockShape n), B.length ≤ D.length → D ≠ B →
        Subsingleton ((T.normalizedJacquetFunctor D).obj
          ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj))) := by
  let := T.topology
  intro A D hlen hne
  exact jacquet_induction_subsingleton_of_geometricLemma T B D (hgeo D)
    (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
    (glCuspidalTensor.{uV, uF} p F T n hn B A).2.2
    (no_associated_refinement_of_size_eq hB D hlen hne)

/-- The vanishing of `induced_jacquet_subsingleton` for every subquotient of
`i_B(A)`. -/
theorem subquotient_jacquet_subsingleton {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (hB : ∀ i i', B.size i = B.size i')
    (hgeo : ∀ D : BlockShape n, GeometricLemmaTheorem.{uF, uV} T B D) :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
      (Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      SmoothRep.IsSubquotient Z
        ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)) →
      ∀ D : BlockShape n, B.length ≤ D.length → D ≠ B →
        Subsingleton ((T.normalizedJacquetFunctor D).obj Z) := by
  let := T.topology
  intro A Z hZ D hlen hne
  have := induced_jacquet_subsingleton T hn B hB hgeo A D hlen hne
  exact subsingleton_of_isSubquotient
    (normalizedJacquetSubquotient.{uF, max uF uV} p F T n D _ Z hZ)

end Vanishing

section OneBlock

/-- The normalized Jacquet module along a one-block shape of the normalized
product over that shape is the external tensor of the factors. -/
def singleBlockInducedJacquetEquiv {n : ℕ} (B : BlockShape n) (hB : B.length = 1) :
    letI := T.topology
    ∀ τ : ∀ t : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size t) F.Carrier),
      ((T.normalizedJacquetFunctor B).obj
          ((T.normalizedProductInductionFunctor B).obj τ)).representation.Equiv
        (FiniteTensor.externalSmoothObject τ).representation := by
  letI := T.topology
  intro τ
  let X := (T.normalizedProductInductionFunctor B).obj τ
  let L := B.singleBlockLeviEquiv hB F.Carrier
  let E := (T.singleBlockNormalizedJacquetEquiv B hB X.representation).symm.trans
    ((T.singleBlockNormalizedInducedEquiv B hB (B.blockTensor fun t => (τ t).representation)
      (FiniteTensor.isSmooth_external _ fun t => (τ t).property)).precomp
      (B.leviEmbedding F.Carrier))
  refine Representation.Equiv.mk E.toLinearEquiv ?_
  intro m
  have hm : L.symm (B.leviEmbedding F.Carrier m) = m := L.symm_apply_apply m
  have hE := E.isIntertwining' m
  change E.toLinearMap ∘ₗ _ =
    (B.blockTensor fun t => (τ t).representation) (L.symm (B.leviEmbedding F.Carrier m)) ∘ₗ
      E.toLinearMap at hE
  rw [hm] at hE
  exact hE

end OneBlock

section Transport

/-- Transport of a property of a shape with two factor families along an
equality of ranks, with heterogeneously equal shapes and families. -/
theorem shape_family_transport {a b : ℕ} (h : a = b) {B : BlockShape a} {B' : BlockShape b}
    (hB : HEq B B') :
    letI := T.topology
    ∀ {τ υ : ∀ t : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size t) F.Carrier)}
      {τ' υ' : ∀ t : Fin B'.length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B'.size t) F.Carrier)},
      HEq τ τ' → HEq υ υ' →
      ∀ Q : ∀ (n : ℕ) (C : BlockShape n),
          (∀ t : Fin C.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size t) F.Carrier)) →
          (∀ t : Fin C.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size t) F.Carrier)) →
            Prop,
        Q a B τ υ → Q b B' τ' υ' := by
  subst h
  obtain rfl := eq_of_heq hB
  intro τ υ τ' υ' hτ hυ Q hQ
  obtain rfl := eq_of_heq hτ
  obtain rfl := eq_of_heq hυ
  exact hQ

/-- A shape is heterogeneously equal to its rank transport. -/
theorem heq_rankCast {a b : ℕ} (h : a = b) (B : BlockShape a) : HEq B (B.rankCast h) := by
  subst h
  rfl

end Transport

section Slots

variable {m r : ℕ} (hr : 0 < r) (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)

/-- The product, over slot `j` of the merged shape, of the original block factors
inside that slot: `i_{S_j}(σ_{e(j,0)}, …)` for `S = adjacentRefinement` and
`e = adjacentBlockEquiv`. -/
abbrev slotProduct
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor
    ((BlockShape.uniform m r hr).adjacentRefinement k hk j)).obj
    (fun t => σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩))

/-- The uniform block factors with blocks `k` and `k + 1` exchanged. -/
abbrev swappedFactors
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier)) :
    letI := T.topology
    ∀ i : Fin (BlockShape.uniform m r hr).length,
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier) :=
  fun i => σ (Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩ i)

/-- Every slot refinement has at most two blocks. -/
theorem slot_length_le (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length)
    {n : ℕ} (D : BlockShape n) (hD : 1 < D.length) :
    ((BlockShape.uniform m r hr).adjacentRefinement k hk j).length ≤ D.length := by
  rw [BlockShape.adjacentRefinement_length]
  split_ifs <;> omega

/-- (H1) for every subquotient of a slot product of supercuspidal factors, from
the geometric lemma. -/
theorem slot_subquotient_jacquet_subsingleton (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation)
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) :
    letI := T.topology
    ∀ Z : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier),
      SmoothRep.IsSubquotient Z (slotProduct T hr k hk σ j) →
      ∀ D : BlockShape (((BlockShape.uniform m r hr).adjacentMerge k hk).size j),
        1 < D.length → D ≠ (BlockShape.uniform m r hr).adjacentRefinement k hk j →
          Subsingleton ((T.normalizedJacquetFunctor D).obj Z) := by
  let := T.topology
  intro Z hZ D hD hne
  have hn := ((BlockShape.uniform m r hr).adjacentMerge k hk).positive j
  exact subquotient_jacquet_subsingleton T hn
    ((BlockShape.uniform m r hr).adjacentRefinement k hk j) (fun _ _ => rfl)
    (fun D => hgeo p F T _ hn _ D)
    (fun t => ⟨σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩), hσ _⟩)
    Z hZ D (slot_length_le hr k hk j D hD) hne

/-- (H1) for a slot product of supercuspidal factors, from the geometric lemma. -/
theorem slot_jacquet_subsingleton (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation)
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) :
    letI := T.topology
    ∀ D : BlockShape (((BlockShape.uniform m r hr).adjacentMerge k hk).size j),
      1 < D.length → D ≠ (BlockShape.uniform m r hr).adjacentRefinement k hk j →
        Subsingleton ((T.normalizedJacquetFunctor D).obj (slotProduct T hr k hk σ j)) := by
  let := T.topology
  intro D hD hne
  have hn := ((BlockShape.uniform m r hr).adjacentMerge k hk).positive j
  exact induced_jacquet_subsingleton T hn
    ((BlockShape.uniform m r hr).adjacentRefinement k hk j) (fun _ _ => rfl)
    (fun D => hgeo p F T _ hn _ D)
    (fun t => ⟨σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩), hσ _⟩)
    D (slot_length_le hr k hk j D hD) hne

/-- (H1) for every subrepresentation of a slot product of supercuspidal factors. -/
theorem slot_subrepresentation_jacquet_subsingleton
    (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation)
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) :
    letI := T.topology
    ∀ W : Subrepresentation (slotProduct T hr k hk σ j).representation,
      ∀ D : BlockShape (((BlockShape.uniform m r hr).adjacentMerge k hk).size j),
        1 < D.length → D ≠ (BlockShape.uniform m r hr).adjacentRefinement k hk j →
          Subsingleton ((T.normalizedJacquetFunctor D).obj
            (SmoothRep.subrepresentation (slotProduct T hr k hk σ j) W)) := by
  let := T.topology
  intro W
  exact slot_subquotient_jacquet_subsingleton T hr k hk hgeo σ hσ j _
    (SmoothRep.IsSubrepresentation.isSubquotient
      (SmoothRep.subrepresentation_isSubrepresentation W))

/-- (H1) for every quotient of a slot product of supercuspidal factors. -/
theorem slot_quotient_jacquet_subsingleton
    (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧ IsSupercuspidal (σ i).representation)
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) :
    letI := T.topology
    ∀ W : Subrepresentation (slotProduct T hr k hk σ j).representation,
      ∀ D : BlockShape (((BlockShape.uniform m r hr).adjacentMerge k hk).size j),
        1 < D.length → D ≠ (BlockShape.uniform m r hr).adjacentRefinement k hk j →
          Subsingleton ((T.normalizedJacquetFunctor D).obj
            (SmoothRep.quotient (slotProduct T hr k hk σ j) W)) := by
  let := T.topology
  intro W
  exact slot_subquotient_jacquet_subsingleton T hr k hk hgeo σ hσ j _
    (SmoothRep.IsQuotient.isSubquotient (SmoothRep.quotient_isQuotient W))

/-- (H2) on an unmerged slot: the Jacquet module of the slot product along its
one-block refinement is the external tensor of its factor. -/
theorem slot_jacquet_equiv_of_ne
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) (hj : j.val ≠ k) :
    letI := T.topology
    Nonempty (((T.normalizedJacquetFunctor
        ((BlockShape.uniform m r hr).adjacentRefinement k hk j)).obj
          (slotProduct T hr k hk σ j)).representation.Equiv
      (FiniteTensor.externalSmoothObject (fun t =>
        σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩))).representation) :=
  ⟨singleBlockInducedJacquetEquiv T _
    ((BlockShape.uniform m r hr).adjacentRefinement_length_of_ne k hk j hj) _⟩

/-- Away from the merged slot, exchanging blocks `k` and `k + 1` does not change
the factors of a slot. -/
theorem swappedFactors_slot_of_ne
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) (hj : j.val ≠ k) :
    (fun t => swappedFactors T hr k hk σ
        ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩)) =
      (fun t => σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩)) := by
  funext t
  have ht : t.val = 0 := by
    have h1 := (BlockShape.uniform m r hr).adjacentRefinement_length_of_ne k hk j hj
    have := t.isLt
    omega
  have hv := (BlockShape.uniform m r hr).adjacentBlockEquiv_val k hk ⟨j, t⟩
  dsimp only at hv
  have h1 : ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩).val ≠ k := by
    rw [hv, ht]
    split_ifs <;> omega
  have h2 : ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩).val ≠ k + 1 := by
    rw [hv, ht]
    split_ifs with h <;> omega
  show σ (Equiv.swap _ _ _) = _
  rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (congrArg Fin.val h))
    (fun h => h2 (congrArg Fin.val h))]

/-- (H2) on an unmerged slot, against the exchanged factors. -/
theorem slot_jacquet_equiv_swapped_of_ne
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length) (hj : j.val ≠ k) :
    letI := T.topology
    Nonempty (((T.normalizedJacquetFunctor
        ((BlockShape.uniform m r hr).adjacentRefinement k hk j)).obj
          (slotProduct T hr k hk σ j)).representation.Equiv
      (FiniteTensor.externalSmoothObject (fun t => swappedFactors T hr k hk σ
        ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩))).representation) := by
  rw [swappedFactors_slot_of_ne T hr k hk σ j hj]
  exact slot_jacquet_equiv_of_ne T hr k hk σ j hj

/-- The merged slot has rank `r + r`. -/
theorem merged_size :
    r + r = ((BlockShape.uniform m r hr).adjacentMerge k hk).size
      ((BlockShape.uniform m r hr).adjacentMergeIndex k hk) :=
  ((BlockShape.uniform m r hr).adjacentMerge_size_merged k hk).symm

/-- The refinement of the merged slot is the standard shape `(r, r)`. -/
theorem merged_refinement_heq :
    HEq (Shahidi.twoBlocks r r hr hr)
      ((BlockShape.uniform m r hr).adjacentRefinement k hk
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)) := by
  have hl : ((BlockShape.uniform m r hr).adjacentRefinement k hk
      ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).length = 2 :=
    (BlockShape.uniform m r hr).adjacentRefinement_length_merged k hk
  have heq : (BlockShape.uniform m r hr).adjacentRefinement k hk
      ((BlockShape.uniform m r hr).adjacentMergeIndex k hk) =
        (Shahidi.twoBlocks r r hr hr).rankCast (merged_size hr k hk) := by
    refine BlockShape.ext_of_size hl fun i => ?_
    show r = ![r, r] (Fin.cast hl i)
    generalize Fin.cast hl i = x
    fin_cases x <;> rfl
  rw [heq]
  exact heq_rankCast _ _

/-- The original block inside the merged slot at inner position `t` is block
`k + t`. -/
theorem merged_blockEquiv_val
    (t : Fin ((BlockShape.uniform m r hr).adjacentRefinement k hk
      ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).length) :
    ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk
      ⟨(BlockShape.uniform m r hr).adjacentMergeIndex k hk, t⟩).val = k + t.val := by
  rw [BlockShape.adjacentBlockEquiv_val]
  simp

/-- The factors of the merged slot are the two-block factors `(ρ, ρ')` when
`σ_k = ρ` and `σ_(k+1) = ρ'`. -/
theorem merged_factors_heq
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (ρ ρ' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hρ : letI := T.topology; σ ⟨k, by omega⟩ = ρ)
    (hρ' : letI := T.topology; σ ⟨k + 1, hk⟩ = ρ') :
    letI := T.topology
    HEq (twoBlockFactors hr hr ρ ρ')
      (fun t => σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk
        ⟨(BlockShape.uniform m r hr).adjacentMergeIndex k hk, t⟩)) := by
  have hl : (Shahidi.twoBlocks r r hr hr).length =
      ((BlockShape.uniform m r hr).adjacentRefinement k hk
        ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)).length :=
    ((BlockShape.uniform m r hr).adjacentRefinement_length_merged k hk).symm
  refine Function.hfunext (congrArg Fin hl) fun a a' haa' => ?_
  have hval : a.val = a'.val := (Fin.heq_ext_iff hl).mp haa'
  have hv : ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk
      ⟨(BlockShape.uniform m r hr).adjacentMergeIndex k hk, a'⟩).val = k + a.val := by
    rw [merged_blockEquiv_val hr k hk a', hval]
  fin_cases a
  · have he : (BlockShape.uniform m r hr).adjacentBlockEquiv k hk
        ⟨(BlockShape.uniform m r hr).adjacentMergeIndex k hk, a'⟩ = ⟨k, by omega⟩ :=
      Fin.ext (hv.trans rfl)
    exact (heq_of_eq hρ).symm.trans (congr_arg_heq σ he).symm
  · have he : (BlockShape.uniform m r hr).adjacentBlockEquiv k hk
        ⟨(BlockShape.uniform m r hr).adjacentMergeIndex k hk, a'⟩ = ⟨k + 1, hk⟩ :=
      Fin.ext (hv.trans rfl)
    exact (heq_of_eq hρ').symm.trans (congr_arg_heq σ he).symm

/-- The exchanged factors of the merged slot are the two-block factors
`(ρ', ρ)` when `σ_k = ρ` and `σ_(k+1) = ρ'`. -/
theorem merged_swappedFactors_heq
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (ρ ρ' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hρ : letI := T.topology; σ ⟨k, by omega⟩ = ρ)
    (hρ' : letI := T.topology; σ ⟨k + 1, hk⟩ = ρ') :
    letI := T.topology
    HEq (twoBlockFactors hr hr ρ' ρ)
      (fun t => swappedFactors T hr k hk σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk
        ⟨(BlockShape.uniform m r hr).adjacentMergeIndex k hk, t⟩)) := by
  refine merged_factors_heq T hr k hk (swappedFactors T hr k hk σ) ρ' ρ ?_ ?_
  · show σ (Equiv.swap _ _ _) = ρ'
    rw [Equiv.swap_apply_left]
    exact hρ'
  · show σ (Equiv.swap _ _ _) = ρ
    rw [Equiv.swap_apply_right]
    exact hρ

/-- Ze80 1.11(b), composition clause, at the merged slot: if `σ_k = ρ` and
`σ_(k+1) = ρ'` with `ρ' ≅ νρ` or `ρ ≅ νρ'`, the merged slot product has length
two and exactly one invariant subspace other than zero and the whole space, and
every such subspace and its quotient are irreducible. -/
theorem merged_composition
    (hcomp : TwoSupercuspidalAdjacentProductComposition.{uF, uV} F T)
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hρ : letI := T.topology; σ ⟨k, by omega⟩ = ρ.obj)
    (hρ' : letI := T.topology; σ ⟨k + 1, hk⟩ = ρ'.obj)
    (hadj : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ.isoClass ∨
        ρ.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ'.isoClass) :
    letI := T.topology
    let P := slotProduct T hr k hk σ ((BlockShape.uniform m r hr).adjacentMergeIndex k hk)
    HasCompositionSeriesLength P.obj 2 ∧
      (∃! W : Subrepresentation P.representation, W ≠ ⊥ ∧ W ≠ ⊤) ∧
      ∀ W : Subrepresentation P.representation, W ≠ ⊥ → W ≠ ⊤ →
        (SmoothRep.subrepresentation P W).IsIrreducible ∧
          (SmoothRep.quotient P W).IsIrreducible := by
  let := T.topology
  have hτ := merged_factors_heq T hr k hk σ ρ.obj ρ'.obj hρ hρ'
  exact shape_family_transport T (merged_size hr k hk) (merged_refinement_heq hr k hk) hτ hτ
    (fun n C τ _ =>
      let P := (T.normalizedProductInductionFunctor C).obj τ
      HasCompositionSeriesLength P.obj 2 ∧
        (∃! W : Subrepresentation P.representation, W ≠ ⊥ ∧ W ≠ ⊤) ∧
        ∀ W : Subrepresentation P.representation, W ≠ ⊥ → W ≠ ⊤ →
          (SmoothRep.subrepresentation P W).IsIrreducible ∧
            (SmoothRep.quotient P W).IsIrreducible)
    (hcomp r hr ρ ρ' hadj)

/-- Ze80 1.11(b), Jacquet clause, at the merged slot: (H2) for every invariant
subspace `W` other than zero and the whole space of the merged slot product,
against the factors `σ` for `W` and against the exchanged factors for the
quotient by `W`. -/
theorem merged_jacquet_equiv
    (hjac : TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T)
    (σ : letI := T.topology
      ∀ i : Fin (BlockShape.uniform m r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hρ : letI := T.topology; σ ⟨k, by omega⟩ = ρ.obj)
    (hρ' : letI := T.topology; σ ⟨k + 1, hk⟩ = ρ'.obj)
    (hadj : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ.isoClass ∨
        ρ.isoClass = T.supercuspidalClassRealPowerTwist r 1 ρ'.isoClass) :
    letI := T.topology
    let kk := (BlockShape.uniform m r hr).adjacentMergeIndex k hk
    let P := slotProduct T hr k hk σ kk
    let S := (BlockShape.uniform m r hr).adjacentRefinement k hk kk
    ∀ W : Subrepresentation P.representation, W ≠ ⊥ → W ≠ ⊤ →
      Nonempty (((T.normalizedJacquetFunctor S).obj
          (SmoothRep.subrepresentation P W)).representation.Equiv
        (FiniteTensor.externalSmoothObject (fun t =>
          σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨kk, t⟩))).representation) ∧
      Nonempty (((T.normalizedJacquetFunctor S).obj
          (SmoothRep.quotient P W)).representation.Equiv
        (FiniteTensor.externalSmoothObject (fun t => swappedFactors T hr k hk σ
          ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨kk, t⟩))).representation) := by
  let := T.topology
  exact shape_family_transport T (merged_size hr k hk) (merged_refinement_heq hr k hk)
    (merged_factors_heq T hr k hk σ ρ.obj ρ'.obj hρ hρ')
    (merged_swappedFactors_heq T hr k hk σ ρ.obj ρ'.obj hρ hρ')
    (fun n C τ υ =>
      let P := (T.normalizedProductInductionFunctor C).obj τ
      ∀ W : Subrepresentation P.representation, W ≠ ⊥ → W ≠ ⊤ →
        Nonempty (((T.normalizedJacquetFunctor C).obj
            (SmoothRep.subrepresentation P W)).representation.Equiv
          (FiniteTensor.externalSmoothObject τ).representation) ∧
        Nonempty (((T.normalizedJacquetFunctor C).obj
            (SmoothRep.quotient P W)).representation.Equiv
          (FiniteTensor.externalSmoothObject υ).representation))
    (hjac r hr ρ ρ' hadj)

end Slots

end Langlands.Classification.SegmentEdge
