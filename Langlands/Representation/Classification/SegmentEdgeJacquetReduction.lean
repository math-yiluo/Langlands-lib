import Langlands.Representation.Classification.SegmentEdgeCombinatorics
import Langlands.Representation.Classification.SegmentEdgeJacquetStatement
import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.Parabolic.RefinedJacquetTensor
import Langlands.Representation.Tensor.FiniteRegrouping
import Langlands.Representation.Tensor.ProductFiltration
import Langlands.Representation.Filtration.ZeroFactorDeletionProof

/-!
# The merged-slot Jacquet filtration from the geometric lemma

Let `Γ` merge blocks `k` and `k + 1` of a block shape `B` in which no two blocks
fit together into one block. For factors `Y_j` of `Γ` satisfying the hypotheses
(H1) and (H2) of `SegmentEdgeJacquetFiltration`, this module derives the
filtration of the normalized `B` Jacquet module of `i_Γ(Y)` from the geometric
lemma `GeometricLemmaTheorem T Γ B` and the proved zero-factor deletion.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.SegmentEdge

open GeneralLinear Geometric CuspidalSupport CategoryTheory

universe uF uV uW

section Helpers

/-- Equality relabeling preserves an equivalence with a representation pulled
back along a homomorphism. -/
def subgroupEqualityCompEquiv {G : Type uF} [Group G] [TopologicalSpace G]
    {M : Type*} [Monoid M] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H K : Subgroup G) (h : H = K) (A : SmoothRep.{0, uF, uW} ℂ H)
    (τ : Representation ℂ M V) (ψ : H →* M) (e : A.representation.Equiv (τ.comp ψ)) :
    ((subgroupEqualityFunctor H K h).obj A).representation.Equiv
      (τ.comp (ψ.comp (MulEquiv.subgroupCongr h).symm.toMonoidHom)) := by
  subst K
  exact e

/-- An indexed tensor product with one zero factor is zero. -/
theorem piTensorProduct_subsingleton {ι : Type*} {R : Type*} [CommRing R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (j : ι) [Subsingleton (M j)] : Subsingleton (PiTensorProduct R M) := by
  classical
  have h : ∀ z : PiTensorProduct R M, z = 0 := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [MultilinearMap.map_coord_zero (PiTensorProduct.tprod R) j
        (Subsingleton.elim _ _), smul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩

end Helpers

section Transport

variable {F : Type uF} [Field F] {n : ℕ}

/-- Intersection transport of a representation pulled back from a third Levi
`D` along a homomorphism compatible with the ambient embeddings. -/
def intersectionTransportEquivOf (B C D : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) D C w) (ψ : sourceLevi F B C w →* D.Levi F)
    (hψ : ∀ x, D.leviEmbedding F (ψ x) = B.leviEmbedding F x.val)
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (sourceLevi F B C w) W) (ρ : Representation ℂ (D.Levi F) V)
    (e : σ.Equiv (ρ.comp ψ)) :
    (intersectionTransport F B C w σ).Equiv
      ((transport D C w hw ρ).comp (sourceLevi F C B w⁻¹).subtype) := by
  have key : ∀ m : sourceLevi F C B w⁻¹,
      ψ ((intersectionLeviConjugation F B C w).symm m) =
        (leviConjugation D C w hw).symm m.val := by
    intro m
    apply D.leviEmbedding_injective F
    rw [hψ, intersectionLeviConjugation_symm_embedding, leviConjugation_symm_embedding]
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro m
  apply LinearMap.ext
  intro v
  have he := LinearMap.congr_fun
    (e.isIntertwining' ((intersectionLeviConjugation F B C w).symm m)) v
  change e (σ ((intersectionLeviConjugation F B C w).symm m) v) =
    ρ ((leviConjugation D C w hw).symm m.val) (e v)
  change e (σ ((intersectionLeviConjugation F B C w).symm m) v) =
    ρ (ψ ((intersectionLeviConjugation F B C w).symm m)) (e v) at he
  rw [key] at he
  exact he

variable (B : BlockShape n) (k : ℕ) (hk : k + 1 < B.length)

/-- The Levi of `B` lies in the Levi of the merged shape. -/
theorem leviSubgroup_le_merge :
    B.leviSubgroup F ≤ (B.adjacentMerge k hk).leviSubgroup F := by
  intro g hg
  rw [levi_mem_iff] at hg ⊢
  intro a b hab
  exact hg a b (fun h => hab (mergeBlock_eq_of_blockIndex_eq B k hk h))

/-- A permutation conjugating the Levi of `B` onto itself has full target
intersection with the merged shape. -/
theorem sourceLevi_merge_eq_top (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B B w) :
    sourceLevi F B (B.adjacentMerge k hk) w⁻¹ = ⊤ := by
  have h1 := targetLevi_eq_top_of_conjugates (F := F) B B w hw
  apply top_unique
  intro m _
  have hm : m ∈ sourceLevi F B B w⁻¹ := h1 ▸ Subgroup.mem_top m
  exact leviSubgroup_le_merge B k hk hm

/-- Regrouping the factors of the Levi of `B` along the merged blocks is the
nested block-diagonal inclusion of the adjacent refinement. -/
theorem leviEmbedding_regroup (m : ∀ j, (B.adjacentRefinement k hk j).Levi F) :
    B.leviEmbedding F ((FiniteTensor.regroupGroup (fun i => GeneralLinear (B.size i) F)
        (B.adjacentBlockEquiv k hk)).symm m) =
      (B.adjacentMerge k hk).leviEmbedding F
        (fun j => (B.adjacentRefinement k hk j).leviEmbedding F (m j)) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨j, a⟩, rfl⟩ := (B.adjacentMerge k hk).indexEquiv.surjective x
  obtain ⟨⟨t, a⟩, rfl⟩ := (B.adjacentRefinement k hk j).indexEquiv.surjective a
  obtain ⟨⟨j', b⟩, rfl⟩ := (B.adjacentMerge k hk).indexEquiv.surjective y
  obtain ⟨⟨t', b⟩, rfl⟩ := (B.adjacentRefinement k hk j').indexEquiv.surjective b
  change B.leviEmbedding F _
      ((B.adjacentMerge k hk).index j ((B.adjacentRefinement k hk j).index t a))
      ((B.adjacentMerge k hk).index j' ((B.adjacentRefinement k hk j').index t' b)) =
    (B.adjacentMerge k hk).leviEmbedding F _
      ((B.adjacentMerge k hk).index j ((B.adjacentRefinement k hk j).index t a))
      ((B.adjacentMerge k hk).index j' ((B.adjacentRefinement k hk j').index t' b))
  by_cases hj : j = j'
  · subst j'
    rw [(B.adjacentMerge k hk).leviEmbedding_apply_same]
    by_cases ht : t = t'
    · subst t'
      rw [(B.adjacentRefinement k hk j).leviEmbedding_apply_same,
        BlockShape.adjacent_index, BlockShape.adjacent_index,
        B.leviEmbedding_apply_same, FiniteTensor.regroupGroup_symm_apply_image]
      rfl
    · rw [(B.adjacentRefinement k hk j).leviEmbedding_apply_ne F _ a b ht,
        BlockShape.adjacent_index, BlockShape.adjacent_index,
        B.leviEmbedding_apply_ne]
      intro h
      apply ht
      have := (B.adjacentBlockEquiv k hk).injective h
      rw [Sigma.mk.inj_iff] at this
      exact eq_of_heq this.2
  · rw [(B.adjacentMerge k hk).leviEmbedding_apply_ne F _ _ _ hj,
      BlockShape.adjacent_index, BlockShape.adjacent_index,
      B.leviEmbedding_apply_ne]
    intro h
    apply hj
    have := (B.adjacentBlockEquiv k hk).injective h
    rw [Sigma.mk.inj_iff] at this
    exact this.1

/-- The homomorphism from the adjacent refined Levi of the merged shape to the
Levi of `B`, regrouping the inner blocks. -/
def refinedToLevi :
    refinedLevi F (B.adjacentMerge k hk) (B.adjacentRefinement k hk) →* B.Levi F :=
  (FiniteTensor.regroupGroup (fun i => GeneralLinear (B.size i) F)
      (B.adjacentBlockEquiv k hk)).symm.toMonoidHom.comp
    (refinedLeviEquiv F (B.adjacentMerge k hk) (B.adjacentRefinement k hk)).symm.toMonoidHom

theorem leviEmbedding_refinedToLevi
    (x : refinedLevi F (B.adjacentMerge k hk) (B.adjacentRefinement k hk)) :
    B.leviEmbedding F (refinedToLevi B k hk x) = (B.adjacentMerge k hk).leviEmbedding F x.val := by
  change B.leviEmbedding F ((FiniteTensor.regroupGroup (fun i => GeneralLinear (B.size i) F)
      (B.adjacentBlockEquiv k hk)).symm
        ((refinedLeviEquiv F (B.adjacentMerge k hk) (B.adjacentRefinement k hk)).symm x)) = _
  rw [leviEmbedding_regroup]
  congr 1
  exact congrArg Subtype.val
    ((refinedLeviEquiv F (B.adjacentMerge k hk) (B.adjacentRefinement k hk)).apply_symm_apply x)

end Transport

section Pieces

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The upper normalized refined Jacquet module of an external tensor product
vanishes when one factor Jacquet module vanishes. -/
theorem refinedJacquet_external_subsingleton {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) :
    letI := T.topology
    ∀ (Y : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (j : Fin B.length),
      Subsingleton ((T.normalizedJacquetFunctor (S j)).obj (Y j)) →
      Subsingleton ((T.normalizedRefinedJacquetFunctor B S).obj
        (FiniteTensor.externalSmoothObject Y)) := by
  let := T.topology
  intro Y j hj
  have h1 : Subsingleton ((S j).JacquetModule (Y j).obj.ρ) := hj
  have h2 : Subsingleton (PiTensorProduct ℂ (fun i => (S i).JacquetModule (Y i).obj.ρ)) :=
    piTensorProduct_subsingleton j
  exact (RefinedJacquetTensor.refinedCoinvariantsEquiv B S (fun i => (Y i).obj)).injective.subsingleton

/-- A geometric piece vanishes when its inner refined Jacquet module vanishes. -/
theorem geometricPiece_subsingleton {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      Subsingleton ((T.normalizedRefinedJacquetFunctor B S).obj A) →
      Subsingleton ((geometricPieceFunctor T B C w S R hS hR).obj A) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A hJ
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  have hJ' : Subsingleton J' := subgroupEqualityFunctor_subsingleton _ _ _ J
  let W := (intersectionTransportFunctor F.Carrier B C w).obj J'
  have hW : Subsingleton W := hJ'
  let W' := (subgroupEqualityFunctor _ _ hR).obj W
  have hW' : Subsingleton W' := subgroupEqualityFunctor_subsingleton _ _ _ W
  exact normalizedRefinedInductionFunctor_subsingleton F T C R W' hW'

variable {n : ℕ} (B : BlockShape n) (k : ℕ) (hk : k + 1 < B.length)

/-- The upper normalized adjacent refined Jacquet module of the merged factors,
when each factor Jacquet module is the tensor product of the original block
factors, is the tensor product of all block factors pulled back along
`refinedToLevi`. -/
def mergedJacquetEquiv
    (A : ∀ j, Rep.{uW} ℂ (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (H : ∀ j, (T.normalizedJacquet (B.adjacentRefinement k hk j) (A j).ρ).Equiv
      (FiniteTensor.external (fun t => ρ (B.adjacentBlockEquiv k hk ⟨j, t⟩)))) :
    Representation.Equiv
      (T.normalizedRefinedJacquet (B.adjacentMerge k hk) (B.adjacentRefinement k hk)
        (FiniteTensor.external fun j => (A j).ρ))
      ((FiniteTensor.external ρ).comp (refinedToLevi B k hk)) :=
  ((RefinedJacquetTensor.jacquetEquiv T (B.adjacentMerge k hk) (B.adjacentRefinement k hk) A).trans
    (FiniteTensorFiltration.compCongr (FiniteTensorFiltration.externalCongr H)
      (refinedLeviEquiv F.Carrier (B.adjacentMerge k hk)
        (B.adjacentRefinement k hk)).symm.toMonoidHom)).trans
    (FiniteTensorFiltration.compCongr (FiniteTensor.regroupEquiv (B.adjacentBlockEquiv k hk) ρ).symm
      (refinedLeviEquiv F.Carrier (B.adjacentMerge k hk)
        (B.adjacentRefinement k hk)).symm.toMonoidHom)

set_option maxHeartbeats 1600000 in
/-- A geometric piece of a Levi-conjugating permutation with adjacent source
refinement is the Weyl transport of the tensor product of the block factors. -/
theorem geometricPiece_equiv_of_conjugates :
    letI := T.topology
    ∀ (σ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (Y : ∀ j, SmoothRep.{0, uF, uW} ℂ
        (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier)),
      (∀ j, Nonempty (((T.normalizedJacquetFunctor (B.adjacentRefinement k hk j)).obj
          (Y j)).representation.Equiv
        (FiniteTensor.externalSmoothObject (fun t =>
          σ (B.adjacentBlockEquiv k hk ⟨j, t⟩))).representation)) →
      ∀ (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F.Carrier) B B w)
        (S : BlockRefinement (B.adjacentMerge k hk)) (R : BlockRefinement B)
        (hS : sourceLevi F.Carrier (B.adjacentMerge k hk) B w =
          refinedLevi F.Carrier (B.adjacentMerge k hk) S)
        (hR : sourceLevi F.Carrier B (B.adjacentMerge k hk) w⁻¹ = refinedLevi F.Carrier B R),
        S = B.adjacentRefinement k hk →
        Nonempty (((geometricPieceFunctor T (B.adjacentMerge k hk) B w S R hS hR).obj
            (FiniteTensor.externalSmoothObject Y)).ρ.Equiv
          (transport B B w hw (FiniteTensor.externalSmoothObject σ).representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro σ Y H2 w hw S R hS hR hSeq
  subst hSeq
  have H2' : ∀ j, (T.normalizedJacquet (B.adjacentRefinement k hk j) (Y j).obj.ρ).Equiv
      (FiniteTensor.external (fun t => (σ (B.adjacentBlockEquiv k hk ⟨j, t⟩)).obj.ρ)) :=
    fun j => (H2 j).some
  have eJ := mergedJacquetEquiv T B k hk (fun j => (Y j).obj) (fun i => (σ i).obj.ρ) H2'
  let J := (T.normalizedRefinedJacquetFunctor (B.adjacentMerge k hk)
    (B.adjacentRefinement k hk)).obj (FiniteTensor.externalSmoothObject Y)
  let ρσ := (FiniteTensor.externalSmoothObject σ).representation
  have eJ0 : J.representation.Equiv (ρσ.comp (refinedToLevi B k hk)) := eJ
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  let ψ := (refinedToLevi (F := F.Carrier) B k hk).comp
    (MulEquiv.subgroupCongr hS.symm).symm.toMonoidHom
  have hψ : ∀ x, B.leviEmbedding F.Carrier (ψ x) =
      (B.adjacentMerge k hk).leviEmbedding F.Carrier x.val :=
    fun x => leviEmbedding_refinedToLevi B k hk ((MulEquiv.subgroupCongr hS.symm).symm x)
  have eJ' : J'.representation.Equiv (ρσ.comp ψ) :=
    subgroupEqualityCompEquiv _ _ hS.symm J ρσ (refinedToLevi B k hk) eJ0
  let τ := transport B B w hw ρσ
  let Q := (intersectionTransportFunctor F.Carrier (B.adjacentMerge k hk) B w).obj J'
  have eQ : Q.representation.Equiv
      (τ.comp (sourceLevi F.Carrier B (B.adjacentMerge k hk) w⁻¹).subtype) :=
    intersectionTransportEquivOf (B.adjacentMerge k hk) B B w hw ψ hψ J'.representation ρσ eJ'
  let Q' := (subgroupEqualityFunctor _ _ hR).obj Q
  have eQ' : Q'.representation.Equiv (τ.comp (refinedLevi F.Carrier B R).subtype) :=
    subgroupEqualityEquiv _ _ hR Q τ eQ
  have hfullR : refinedLevi F.Carrier B R = ⊤ :=
    hR.symm.trans (sourceLevi_merge_eq_top B k hk w hw)
  have hτ : IsSmooth τ :=
    isSmooth_transport B B w hw (FiniteTensor.externalSmoothObject σ).isSmooth
  change Nonempty ((T.normalizedRefinedInduced B R Q'.representation).Equiv τ)
  exact ⟨fullRefinedInductionEquiv T B R hfullR Q'.representation τ eQ' hτ⟩

end Pieces

section Assembly

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

set_option maxHeartbeats 1600000 in
/-- The merged-slot filtration for a general block shape in which no two blocks
fit together into one block, from the geometric lemma for `(Γ, B)`. -/
theorem edgeFiltration_of_geometricLemma {n : ℕ} (B : BlockShape n) (k : ℕ)
    (hk : k + 1 < B.length)
    (hsize : ∀ c c' d : Fin B.length, c ≠ c' → B.size d < B.size c + B.size c')
    (hgeo : GeometricLemmaTheorem.{uF, uW} T (B.adjacentMerge k hk) B) :
    letI := T.topology
    ∀ (σ : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (Y : ∀ j, SmoothRep.{0, uF, uW} ℂ
        (GeneralLinear ((B.adjacentMerge k hk).size j) F.Carrier)),
      (∀ j (D : BlockShape ((B.adjacentMerge k hk).size j)),
        1 < D.length → D ≠ B.adjacentRefinement k hk j →
          Subsingleton ((T.normalizedJacquetFunctor D).obj (Y j))) →
      (∀ j, Nonempty (((T.normalizedJacquetFunctor (B.adjacentRefinement k hk j)).obj
          (Y j)).representation.Equiv
        (FiniteTensor.externalSmoothObject (fun t =>
          σ (B.adjacentBlockEquiv k hk ⟨j, t⟩))).representation)) →
      ∃ (N : ℕ) (e : Fin N ≃ {v : MinimalConjugatingPermutations (F := F.Carrier) B B //
            IsMinimalRepresentative (B.adjacentMerge k hk) B v.val.val})
        (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor B).obj
            ((T.normalizedProductInductionFunctor (B.adjacentMerge k hk)).obj Y)).representation) N),
        ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (transport B B (e i).val.val.val (e i).val.property
            (FiniteTensor.externalSmoothObject σ).representation)) := by
  let := T.topology
  intro σ Y H1 H2
  obtain ⟨S, R, hS, hR, m, e, order, s, hs⟩ := hgeo
  let enum : Fin m ≃ MinimalRepresentatives (B.adjacentMerge k hk) B := order.trans e
  let ρY := FiniteTensor.externalSmoothObject Y
  let evaluated := objectFiltrationAt s ρY
  have graded (i : Fin m) :
      Nonempty ((evaluated.gradedRepresentation i).ρ.Equiv
        ((geometricPieceFunctor T (B.adjacentMerge k hk) B (enum i).val (S (enum i))
          (R (enum i)) (hS (enum i)).2.1 (hR (enum i)).2.1).obj ρY).ρ) := by
    obtain ⟨iso⟩ := hs i
    exact ⟨Representation.equivOfIso (iso.app ρY)⟩
  let P : Fin m → Prop := fun i => ConjugatesLevi (F := F.Carrier) B B (enum i).val
  have zero (i : Fin m) (hi : ¬ P i) : Subsingleton (evaluated.gradedRepresentation i) := by
    obtain ⟨j, hj1, hj2⟩ := exists_bad_block_of_not_conjugatesLevi B k hk hsize
      (enum i).val (S (enum i)) (hS (enum i)).2.1 hi
    have hJ := refinedJacquet_external_subsingleton T (B.adjacentMerge k hk) (S (enum i)) Y j
      (H1 j (S (enum i) j) hj1 hj2)
    have hP := geometricPiece_subsingleton T (B.adjacentMerge k hk) B (enum i).val
      (S (enum i)) (R (enum i)) (hS (enum i)).2.1 (hR (enum i)).2.1 ρY hJ
    obtain ⟨f⟩ := graded i
    exact f.toLinearEquiv.injective.subsingleton
  obtain ⟨N, retained, t, ht⟩ :=
    ObjectRepFiltration.zeroFactorDeletionTheorem ℂ (B.Levi F.Carrier) _ m evaluated P zero
  let selected : {i : Fin m // P i} ≃
      {w : MinimalRepresentatives (B.adjacentMerge k hk) B //
        ConjugatesLevi (F := F.Carrier) B B w.val} :=
    enum.subtypeEquiv (fun _ => Iff.rfl)
  let indexing := (retained.trans selected).trans (retainedEquiv (F := F.Carrier) B k hk)
  refine ⟨N, indexing, t, fun j => ?_⟩
  obtain ⟨f⟩ := ht j
  obtain ⟨g⟩ := graded (retained j).val
  have hw : P (retained j).val := (retained j).property
  obtain ⟨h⟩ := geometricPiece_equiv_of_conjugates T B k hk σ Y H2
    (enum (retained j).val).val hw (S (enum (retained j).val)) (R (enum (retained j).val))
    (hS (enum (retained j).val)).2.1 (hR (enum (retained j).val)).2.1
    (eq_adjacentRefinement_of_conjugatesLevi B k hk _ _ (hS (enum (retained j).val)).2.1 hw)
  exact ⟨(f.trans g).trans h⟩

/-- Statement (E) from the geometric lemma for every merged-slot pair of the
uniform shapes. -/
theorem segmentEdgeJacquetFiltration_of_geometricLemma
    (hgeo : ∀ (m r : ℕ) (hr : 0 < r) (k : ℕ)
      (hk : k + 1 < (BlockShape.uniform m r hr).length),
      GeometricLemmaTheorem.{uF, uW} T ((BlockShape.uniform m r hr).adjacentMerge k hk)
        (BlockShape.uniform m r hr)) :
    SegmentEdgeJacquetFiltration.{uF, uV, uW} F T := by
  intro m r hr k hk
  exact edgeFiltration_of_geometricLemma F T (BlockShape.uniform m r hr) k hk
    (uniform_size_lt m r hr) (hgeo m r hr k hk)

/-- Statement (E) from the normalized geometric lemma over all p-adic fields. -/
theorem segmentEdgeJacquetFiltration_of_padicGeometricLemma
    (hgeo : PadicGeometricLemmaTheorem.{uF, uW}) :
    SegmentEdgeJacquetFiltration.{uF, uV, uW} F T := by
  apply segmentEdgeJacquetFiltration_of_geometricLemma
  intro m r hr k hk
  have hm : 0 < m * r := Nat.mul_pos (by
    have : k + 1 < m := hk
    omega) hr
  exact hgeo p F T (m * r) hm _ _

end Assembly

end Langlands.Classification.SegmentEdge
