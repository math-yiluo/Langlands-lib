import Langlands.Representation.Classification.SegmentFullJacquetCentral
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.Classification.SegmentTensorStabilizerProof
import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.Geometric.WeylUniquenessProof

/-!
# The full cuspidal Jacquet module of a segment induction, split by a central element

From the associated Jacquet filtration of `r_β(i(A, νA, …, ν^(m-1) A))`, whose
graded pieces are the Weyl transports of `A ⊗ νA ⊗ ⋯ ⊗ ν^(m-1) A`, the separating
block scalar acts on the pieces by pairwise distinct scalars.
-/

noncomputable section

namespace Langlands.SegmentFullJacquet

open GeneralLinear Geometric CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The block map of a minimal self-conjugating permutation of the uniform shape,
as a permutation of the blocks. -/
def blockPerm {m r : ℕ} {hr : 0 < r}
    (w : MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr)) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (α := Fin m) (β := Fin m)
    (blockMap (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) w.val.val)
    (TotalConjugatingCount.blockMap_bijective w.property)

theorem blockPerm_apply {m r : ℕ} {hr : 0 < r}
    (w : MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr)) (i : Fin m) :
    blockPerm F w i =
      blockMap (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) w.val.val i := rfl

theorem blockPerm_injective {m r : ℕ} {hr : 0 < r} :
    Function.Injective (blockPerm F (m := m) (r := r) (hr := hr)) := by
  intro w w' h
  have hx := TotalConjugatingCount.eq_of_blockValue_eq (F := F.Carrier)
    (BlockShape.uniform m r hr) ⟨_, w⟩ ⟨_, w'⟩ (fun i => by
      change (blockPerm F w i : ℕ) = (blockPerm F w' i : ℕ)
      rw [h])
  exact eq_of_heq (Sigma.mk.inj_iff.mp hx).2

/-- Every permutation of the blocks of the uniform shape is the block map of a
minimal self-conjugating permutation, the canonical block reordering. -/
theorem blockPerm_surjective {m r : ℕ} {hr : 0 < r} :
    Function.Surjective (blockPerm F (m := m) (r := r) (hr := hr)) := by
  intro g
  have hperm : (BlockShape.uniform m r hr).permute g.symm = BlockShape.uniform m r hr :=
    BlockShape.ext_of_size rfl fun _ => rfl
  have hmin := isMinimalRepresentative_blockPermutation (BlockShape.uniform m r hr) g.symm
  have hconj := conjugatesLevi_blockPermutation (F := F.Carrier) (BlockShape.uniform m r hr) g.symm
  have hidx := blockIndex_blockPermutation (BlockShape.uniform m r hr) g.symm
  have hval : ∀ x, (blockIndex ((BlockShape.uniform m r hr).permute g.symm) x : ℕ) =
      (blockIndex (BlockShape.uniform m r hr) x : ℕ) := fun x => by rw [hperm]
  rw [hperm] at hmin hconj
  refine ⟨⟨⟨(BlockShape.uniform m r hr).blockPermutation g.symm, hmin⟩, hconj⟩, ?_⟩
  ext i
  change (blockIndex (BlockShape.uniform m r hr)
    ((BlockShape.uniform m r hr).blockPermutation g.symm
      ((BlockShape.uniform m r hr).index i ⟨0, hr⟩)) : ℕ) = g i
  rw [← hval, congrArg Fin.val (hidx _)]
  have hb := blockIndex_index (BlockShape.uniform m r hr) i ⟨0, hr⟩
  exact congrArg (fun j => ((g.symm.symm j : Fin m) : ℕ)) hb

/-- A minimal self-conjugating permutation of the uniform shape is also minimal for
the shape merging blocks `k` and `k + 1` exactly when it keeps their order. -/
theorem isMinimalRepresentative_adjacentMerge_iff {m r : ℕ} {hr : 0 < r} (k : ℕ)
    (hk : k + 1 < (BlockShape.uniform m r hr).length)
    (w : MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr)) :
    IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
        (BlockShape.uniform m r hr) w.val.val ↔
      blockPerm F w ⟨k, by simp at hk; omega⟩ < blockPerm F w ⟨k + 1, hk⟩ := by
  have hw := w.property
  have hmin := w.val.property
  rw [isMinimalRepresentative_iff] at hmin ⊢
  have hbi : ∀ a, blockIndex (BlockShape.uniform m r hr) (w.val.val a) =
      blockPerm F w (blockIndex (BlockShape.uniform m r hr) a) :=
    fun a => TotalConjugatingCount.blockIndex_apply hw a
  have hlt : ∀ x y : Fin (m * r), blockIndex (BlockShape.uniform m r hr) x <
      blockIndex (BlockShape.uniform m r hr) y → x < y := fun x y h =>
    lt_of_not_ge fun hyx => absurd (Geometric.blockIndex_monotone _ hyx) (not_le.mpr h)
  have hk0 : k < m := by simp at hk; omega
  have hk1 : k + 1 < m := by simpa using hk
  constructor
  · rintro ⟨h1, -⟩
    have hab := h1 ((BlockShape.uniform m r hr).index ⟨k, hk0⟩ ⟨0, hr⟩)
      ((BlockShape.uniform m r hr).index ⟨k + 1, hk1⟩ ⟨0, hr⟩)
      (by
        rw [BlockShape.blockIndex_adjacentMerge, BlockShape.blockIndex_adjacentMerge,
          blockIndex_index, blockIndex_index, BlockShape.adjacentCollapse_eq_iff]
        right; left
        exact ⟨rfl, rfl⟩)
      (hlt _ _ (by
        rw [blockIndex_index, blockIndex_index]
        exact Fin.lt_def.mpr (by simp)))
    have hle := Geometric.blockIndex_monotone (BlockShape.uniform m r hr) hab.le
    rw [hbi, hbi, blockIndex_index, blockIndex_index] at hle
    refine lt_of_le_of_ne hle fun heq => ?_
    have := congrArg Fin.val ((blockPerm F w).injective heq)
    simp at this
  · intro hg
    refine ⟨fun a b hab hab' => ?_, hmin.2⟩
    rw [BlockShape.blockIndex_adjacentMerge, BlockShape.blockIndex_adjacentMerge,
      BlockShape.adjacentCollapse_eq_iff] at hab
    rcases hab with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hmin.1 a b h hab'
    · apply hlt
      rw [hbi, hbi]
      have ha' : blockIndex (BlockShape.uniform m r hr) a = ⟨k, hk0⟩ := Fin.ext ha
      have hb' : blockIndex (BlockShape.uniform m r hr) b = ⟨k + 1, hk1⟩ := Fin.ext hb
      rw [ha', hb']
      exact hg
    · exfalso
      have := Geometric.blockIndex_monotone (BlockShape.uniform m r hr) hab'.le
      rw [Fin.le_def, ha, hb] at this
      omega

/-- The separating block scalar `diag(ϖ^(m^0) I_r, …, ϖ^(m^(m-1)) I_r)`. -/
def separatingScalar (m r : ℕ) (hr : 0 < r) : (BlockShape.uniform m r hr).Levi F.Carrier :=
  (BlockShape.uniform m r hr).blockScalarLevi F.Carrier (separatingEntries T m)

theorem separatingScalar_comm (m r : ℕ) (hr : 0 < r)
    (g : (BlockShape.uniform m r hr).Levi F.Carrier) :
    separatingScalar F T m r hr * g = g * separatingScalar F T m r hr := by
  funext i
  exact (Subgroup.mem_center_iff.mp (scalarToCenter (separatingEntries T m i)).property
    (g i)).symm

/-- The separating scalar acts on the Weyl transport of the increasing segment
tensor through `segmentScalar` of the block permutation. -/
theorem transport_segment_separatingScalar {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (ω : F.Carrierˣ →* ℂˣ)
    (hω : letI := T.topology
      Classification.HasScalarCharacter A.representation GeneralLinear.scalar ω)
    (w : MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr)) :
    letI := T.topology
    ∀ v, transport _ _ w.val.val w.property
        (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation
        (separatingScalar F T m r hr) v = segmentScalar T ω r m (blockPerm F w) • v := by
  let := T.topology
  intro v
  exact transport_blockTensor_blockScalarLevi w.val.val w.property
    (fun i => T.hasScalarCharacter_segmentFactor A _ hω) _ v

/-- The associated Jacquet filtration of the full cuspidal Jacquet module of the
increasing segment induction, with irreducible graded pieces on which the
separating scalar acts by `segmentScalar` of the block permutation. -/
theorem exists_segmentJacquetFiltration
    (hassoc : AssociatedJacquetFiltrationTheorem.{uF, uV} F T (m * r))
    (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (ω : F.Carrierˣ →* ℂˣ)
    (hω : letI := T.topology
      Classification.HasScalarCharacter A.obj.representation GeneralLinear.scalar ω) :
    letI := T.topology
    ∃ (N : ℕ) (e : Fin N ≃ MinimalConjugatingPermutations (F := F.Carrier)
        (BlockShape.uniform m r hr) (BlockShape.uniform m r hr))
      (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor
        (BlockShape.uniform m r hr)).obj (T.segmentInduced A.obj m hr)).representation) N),
      s.HasSimpleFactors ∧
      (∀ k v, (s.gradedRepresentation k).ρ (separatingScalar F T m r hr) v =
        segmentScalar T ω r m (blockPerm F (e k)) • v) ∧
      ∀ k, Nonempty ((s.gradedRepresentation k).ρ.Equiv
        (transport _ _ (e k).val.val (e k).property
          (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)).representation)) := by
  let := T.topology
  have hσ := Classification.segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A
  obtain ⟨-, N, e, s, hs⟩ := hassoc (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
    (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)) hσ.2.2
    (LevisAssociated.refl _)
  refine ⟨N, e, s, fun k => ?_, fun k v => ?_, hs⟩
  · exact (Langlands.CentralEigenspaceSplitting.isIrreducible_iff_of_equiv (hs k).some).mpr
      (JacquetLength.isIrreducible_transport _ _ hσ.1)
  · exact Langlands.CentralEigenspaceSplitting.apply_eq_smul_of_equiv (hs k).some _ _
      (transport_segment_separatingScalar F T hr A.obj ω hω (e k)) v

end Langlands.SegmentFullJacquet
