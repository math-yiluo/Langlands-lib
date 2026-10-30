import Langlands.Representation.Classification.SegmentFullJacquetEdges
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Classification.ConstituentRelations

/-!
# Assembly of the full cuspidal Jacquet modules of segment constituents

Conditional on the associated Jacquet filtration of the segment induction and on
the Jacquet filtrations of its edge representations, every irreducible
subrepresentation of the increasing segment induction has full cuspidal Jacquet
module equivalent to the increasing segment tensor, and every irreducible quotient
has full cuspidal Jacquet module equivalent to the decreasing segment tensor.
-/

noncomputable section

namespace Langlands.SegmentFullJacquet

open GeneralLinear Geometric CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The segment tensor with its factors permuted is irreducible. -/
theorem isIrreducible_permutedSegmentTensor {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (e : Equiv.Perm (Fin m)) :
    letI := T.topology
    (FiniteTensor.externalSmoothObject
      (fun i => T.segmentFactors A.obj m hr (e i))).representation.IsIrreducible := by
  let := T.topology
  exact (CuspidalSupport.glCuspidalTensor p F T (m * r) (Nat.mul_pos hm hr)
    (BlockShape.uniform m r hr)
    (fun i => Classification.segmentSupercuspidalFactor F T A (((e i : Fin m) : ℕ) : ℝ))).1

/-- A supercuspidal representation has a scalar character on the scalar matrices. -/
theorem exists_hasScalarCharacter {r : ℕ}
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    ∃ ω : F.Carrierˣ →* ℂˣ,
      Classification.HasScalarCharacter A.obj.representation GeneralLinear.scalar ω := by
  let := T.topology
  have := T.generalLinearTopologicalGroup r
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ :=
    admissibleSchur_centralCharacter A.obj.representation A.property.2.1 A.property.1
  exact ⟨χ.comp scalarToCenter, fun z w => hχ (scalarToCenter z) w⟩

/-- Subrepresentation clause, conditional form. Assume the associated Jacquet
filtration of the segment induction, and for every pair of adjacent blocks
`k, k + 1` an edge representation `i_γ(Y)` onto which the segment induction maps
surjectively, whose full cuspidal Jacquet module is filtered by the Weyl
transports of the segment tensor with `k` and `k + 1` swapped, indexed by the
minimal permutations keeping `k` before `k + 1`. Then the full cuspidal Jacquet
module of every irreducible subrepresentation is the increasing segment tensor. -/
theorem subrepresentation_jacquet_equiv
    (hassoc : AssociatedJacquetFiltrationTheorem.{uF, uV} F T (m * r))
    (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hedge : letI := T.topology
      ∀ (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length),
      ∃ (Y : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
          (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier))
        (N : ℕ) (e : Fin N ≃ {v : MinimalConjugatingPermutations (F := F.Carrier)
            (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) //
          IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
            (BlockShape.uniform m r hr) v.val.val})
        (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor
          (BlockShape.uniform m r hr)).obj ((T.normalizedProductInductionFunctor
            ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y)).representation) N),
        (∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (transport _ _ (e i).val.val.val (e i).val.property
            (FiniteTensor.externalSmoothObject (fun i =>
              T.segmentFactors A.obj m hr (adjacentSwap k hk i))).representation))) ∧
        ∃ q : (T.segmentInduced A.obj m hr).representation.IntertwiningMap
            ((T.normalizedProductInductionFunctor
              ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y).representation,
          Function.Surjective q)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (hπ : letI := T.topology
      Classification.IsIrreducibleSubrepresentation
        (T.segmentInduced A.obj m hr).representation π.representation) :
    letI := T.topology
    Nonempty (((T.normalizedJacquetFunctor (BlockShape.uniform m r hr)).obj π).representation.Equiv
      (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)).representation) := by
  let := T.topology
  obtain ⟨ω, hω⟩ := exists_hasScalarCharacter F T A
  obtain ⟨N, eJ, s, hs, hgr, hsEq⟩ := exists_segmentJacquetFiltration F T hassoc hm hr A ω hω
  let bpe := blockPermEquiv F m r hr
  let c : Fin N → ℂ := fun i => segmentScalar T ω r m (blockPerm F (eJ i))
  have hc : Function.Injective c := fun i i' h =>
    eJ.injective (blockPerm_injective F (segmentScalar_injective T ω hr m h))
  obtain ⟨hπirr, j, hj⟩ := hπ
  have hj0 : j ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hπirr
    apply hv
    apply hj
    rw [map_zero, h0]
    rfl
  obtain ⟨f, hf⟩ := exists_jacquet_to_tensor_ne_zero F T hr A.obj π j hj0
  let ι := T.normalizedJacquetMap (BlockShape.uniform m r hr) j
  have hι : Function.Injective ι :=
    normalizedJacquetMap_injective F T _ j (T.segmentInduced A.obj m hr).isSmooth hj
  let i0 : Fin N := eJ.symm (bpe.symm 1)
  have hci0 : c i0 = segmentScalar T ω r m ((1 : Equiv.Perm (Fin m)) : Fin m → Fin m) := by
    simp only [c, i0, Equiv.apply_symm_apply, bpe, blockPerm_blockPermEquiv_symm]
  have hσ : ∀ u, (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)).representation
      (separatingScalar F T m r hr) u = c i0 • u := by
    intro u
    rw [hci0]
    exact blockTensor_blockScalarLevi (fun i => T.hasScalarCharacter_segmentFactor A.obj _ hω) _ u
  refine Nonempty.elim (CentralEigenspaceSplitting.nonempty_equiv_graded_of_sub s
    (separatingScalar F T m r hr) (separatingScalar_comm F T m r hr) c hc hgr hs ι hι f hf i0 hσ ?_)
    (fun φ => ?_)
  swap
  · obtain ⟨ψ⟩ := hsEq i0
    obtain ⟨χ⟩ := nonempty_transport_equiv_permuted F T hr A.obj (eJ i0)
    have h1 : blockPerm F (eJ i0) = 1 := by
      simp only [i0, Equiv.apply_symm_apply, bpe, blockPerm_blockPermEquiv_symm]
    rw [h1] at χ
    exact ⟨(φ.trans ψ).trans χ⟩
  intro i hi
  have hg1 : blockPerm F (eJ i) ≠ 1 := by
    intro h1
    apply hi
    change i = eJ.symm (bpe.symm 1)
    rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply]
    exact h1
  obtain ⟨k, hk, hdesc⟩ := exists_descent_of_ne_one hg1
  obtain ⟨Y, N', e', t, ht, q, hq⟩ := hedge k hk
  let sw : Equiv.Perm (Fin m) := adjacentSwap k hk
  have hsw : sw * sw = 1 := Equiv.swap_mul_self _ _
  let e'' : Fin N' → Fin N := fun jj => eJ.symm (bpe.symm (blockPerm F (e' jj).val * sw))
  refine ⟨_, N', t, e'', fun jj => ?_, ?_, fun jj v => ?_, ?_, ?_, ?_⟩
  · exact (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv (ht jj).some).mpr
      (JacquetLength.isIrreducible_transport _ _
        (isIrreducible_permutedSegmentTensor F T hm hr A sw))
  · intro a b hab
    apply e'.injective
    apply Subtype.ext
    exact blockPerm_injective F (mul_right_cancel (bpe.symm.injective (eJ.symm.injective hab)))
  · have hcj : c (e'' jj) = segmentScalar T ω r m
        ((blockPerm F (e' jj).val * sw.symm : Equiv.Perm (Fin m)) : Fin m → Fin m) := by
      simp only [c, e'', Equiv.apply_symm_apply, bpe, blockPerm_blockPermEquiv_symm, sw,
        adjacentSwap, Equiv.symm_swap]
    rw [hcj]
    exact CentralEigenspaceSplitting.apply_eq_smul_of_equiv (ht jj).some _ _
      (transport_permuted_separatingScalar F T hr A.obj ω hω sw (e' jj).val) v
  · have hv : IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
        (BlockShape.uniform m r hr) (bpe.symm (blockPerm F (eJ i) * sw)).val.val := by
      rw [isMinimalRepresentative_adjacentMerge_iff F k hk]
      simp only [bpe, blockPerm_blockPermEquiv_symm, Equiv.Perm.mul_apply, sw, adjacentSwap,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact hdesc
    refine ⟨e'.symm ⟨bpe.symm (blockPerm F (eJ i) * sw), hv⟩, ?_⟩
    simp only [e'', Equiv.apply_symm_apply, bpe, blockPerm_blockPermEquiv_symm]
    rw [mul_assoc, hsw, mul_one, Equiv.symm_apply_eq, Equiv.symm_apply_eq]
    rfl
  · rintro ⟨jj, hjj⟩
    have h1 : blockPerm F (e' jj).val * sw = 1 := bpe.symm.injective (eJ.symm.injective hjj)
    have h2 : blockPerm F (e' jj).val = sw := by
      have := congrArg (· * sw) h1
      simpa [mul_assoc, hsw] using this
    have hmin := (isMinimalRepresentative_adjacentMerge_iff F k hk (e' jj).val).mp (e' jj).property
    rw [h2] at hmin
    simp only [sw, adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right] at hmin
    exact absurd hmin (by simp [Fin.lt_def])
  · refine ⟨T.normalizedJacquetMap _ q,
      normalizedJacquetMap_surjective F T _ q (T.segmentInduced A.obj m hr).isSmooth hq, ?_⟩
    have hcomp : (T.normalizedJacquetMap _ q).comp ι = T.normalizedJacquetMap _ (q.comp j) :=
      (BlockShape.normalizedJacquetOfMap_comp _ _ j q).symm
    have := hπirr
    rcases Representation.IsIrreducible.injective_or_eq_zero (q.comp j) with hinj | hzero
    · left
      have hJ := normalizedJacquetMap_injective F T (BlockShape.uniform m r hr) _
        ((T.normalizedProductInductionFunctor _).obj Y).isSmooth hinj
      exact fun a b hab => hJ ((DFunLike.congr_fun hcomp a).symm.trans
        (hab.trans (DFunLike.congr_fun hcomp b)))
    · right
      exact hcomp.trans ((congrArg (T.normalizedJacquetMap _) hzero).trans
        (normalizedJacquetMap_zero F T _))

/-- Quotient clause, conditional form. Assume the associated Jacquet filtration
of the segment induction, and for every pair of adjacent blocks `k, k + 1` an
edge representation `i_γ(Y)` mapping injectively into the segment induction,
whose full cuspidal Jacquet module is filtered by the Weyl transports of the
segment tensor indexed by the minimal permutations keeping `k` before `k + 1`.
Then the full cuspidal Jacquet module of every irreducible quotient is the
decreasing segment tensor. -/
theorem quotient_jacquet_equiv
    (hassoc : AssociatedJacquetFiltrationTheorem.{uF, uV} F T (m * r))
    (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hedge : letI := T.topology
      ∀ (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length),
      ∃ (Y : ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear
          (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier))
        (N : ℕ) (e : Fin N ≃ {v : MinimalConjugatingPermutations (F := F.Carrier)
            (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) //
          IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
            (BlockShape.uniform m r hr) v.val.val})
        (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor
          (BlockShape.uniform m r hr)).obj ((T.normalizedProductInductionFunctor
            ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y)).representation) N),
        (∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (transport _ _ (e i).val.val.val (e i).val.property
            (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)).representation))) ∧
        ∃ ι : ((T.normalizedProductInductionFunctor
              ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y).representation.IntertwiningMap
            (T.segmentInduced A.obj m hr).representation,
          Function.Injective ι)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (hπ : letI := T.topology
      Classification.IsIrreducibleQuotient
        (T.segmentInduced A.obj m hr).representation π.representation) :
    letI := T.topology
    Nonempty (((T.normalizedJacquetFunctor (BlockShape.uniform m r hr)).obj π).representation.Equiv
      (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)).representation) := by
  let := T.topology
  obtain ⟨ω, hω⟩ := exists_hasScalarCharacter F T A
  obtain ⟨N, eJ, s, hs, hgr, hsEq⟩ := exists_segmentJacquetFiltration F T hassoc hm hr A ω hω
  let bpe := blockPermEquiv F m r hr
  let c : Fin N → ℂ := fun i => segmentScalar T ω r m (blockPerm F (eJ i))
  have hc : Function.Injective c := fun i i' h =>
    eJ.injective (blockPerm_injective F (segmentScalar_injective T ω hr m h))
  obtain ⟨hπirr, q, hq⟩ := hπ
  have hq0 : q ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible hπirr
    obtain ⟨w, rfl⟩ := hq v
    apply hv
    rw [h0]
    rfl
  obtain ⟨g, hg⟩ := exists_reversedTensor_to_jacquet_ne_zero F T hm hr A.obj A.property.2.1
    π q hq hq0
  let Q := T.normalizedJacquetMap (BlockShape.uniform m r hr) q
  have hQ : Function.Surjective Q :=
    normalizedJacquetMap_surjective F T _ q (T.segmentInduced A.obj m hr).isSmooth hq
  let i0 : Fin N := eJ.symm (bpe.symm Fin.revPerm)
  have hci0 : c i0 = segmentScalar T ω r m ((Fin.revPerm : Equiv.Perm (Fin m)) : Fin m → Fin m) := by
    simp only [c, i0, Equiv.apply_symm_apply, bpe, blockPerm_blockPermEquiv_symm]
  have hσ : ∀ u, ((FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)).representation.comp
      (uniformReverse F m r hr)) (separatingScalar F T m r hr) u = c i0 • u := by
    intro u
    have hUz : uniformReverse F m r hr (separatingScalar F T m r hr) =
        (BlockShape.uniform m r hr).blockScalarLevi F.Carrier
          (fun i => separatingEntries T m (Fin.rev i)) := by
      funext i
      rfl
    rw [hci0, MonoidHom.comp_apply, hUz]
    exact blockTensor_blockScalarLevi (B := BlockShape.uniform m r hr)
      (fun i => T.hasScalarCharacter_segmentFactor A.obj _ hω)
      (fun i => separatingEntries T m (Fin.rev i)) u
  refine Nonempty.elim (CentralEigenspaceSplitting.nonempty_equiv_graded_of_quot s
    (separatingScalar F T m r hr) (separatingScalar_comm F T m r hr) c hc hgr hs Q hQ g hg i0 hσ ?_)
    (fun φ => ?_)
  swap
  · obtain ⟨ψ⟩ := hsEq i0
    obtain ⟨χ⟩ := nonempty_transport_equiv_permuted F T hr A.obj (eJ i0)
    have h1 : blockPerm F (eJ i0) = Fin.revPerm := by
      simp only [i0, Equiv.apply_symm_apply, bpe, blockPerm_blockPermEquiv_symm]
    have hfam : (fun i => T.segmentFactors A.obj m hr ((blockPerm F (eJ i0)).symm i)) =
        T.segmentFactorsDown A.obj m hr := by
      funext i
      rw [h1, Fin.revPerm_symm]
      change T.segmentFactor A.obj (((Fin.rev i : Fin m) : ℕ) : ℝ) =
        T.segmentFactor A.obj ((m - 1 - (i : ℕ) : ℕ) : ℝ)
      congr 2
      rw [Fin.val_rev]
      omega
    rw [hfam] at χ
    exact ⟨(φ.symm.trans ψ).trans χ⟩
  intro i hi
  have hgr' : blockPerm F (eJ i) ≠ Fin.revPerm := by
    intro h1
    apply hi
    change i = eJ.symm (bpe.symm Fin.revPerm)
    rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply]
    exact h1
  obtain ⟨k, hk, hasc⟩ := exists_ascent_of_ne_rev hgr'
  obtain ⟨Y, N', e', t, ht, ι', hι'⟩ := hedge k hk
  let e'' : Fin N' → Fin N := fun jj => eJ.symm (e' jj).val
  have hσirr := (Classification.segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A).1
  refine ⟨_, N', t, e'', fun jj => ?_, ?_, fun jj v => ?_, ?_, ?_, ?_⟩
  · exact (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv (ht jj).some).mpr
      (JacquetLength.isIrreducible_transport _ _ hσirr)
  · intro a b hab
    exact e'.injective (Subtype.ext (eJ.symm.injective hab))
  · have hcj : c (e'' jj) = segmentScalar T ω r m (blockPerm F (e' jj).val) := by
      simp only [c, e'', Equiv.apply_symm_apply]
    rw [hcj]
    exact CentralEigenspaceSplitting.apply_eq_smul_of_equiv (ht jj).some _ _
      (transport_segment_separatingScalar F T hr A.obj ω hω (e' jj).val) v
  · have hv : IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
        (BlockShape.uniform m r hr) (eJ i).val.val :=
      (isMinimalRepresentative_adjacentMerge_iff F k hk (eJ i)).mpr hasc
    refine ⟨e'.symm ⟨eJ i, hv⟩, ?_⟩
    simp only [e'', Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · rintro ⟨jj, hjj⟩
    have h1 : (e' jj).val = bpe.symm Fin.revPerm := eJ.symm.injective hjj
    have h2 : blockPerm F (e' jj).val = Fin.revPerm := by
      rw [h1]
      exact blockPerm_blockPermEquiv_symm F m r hr _
    have hmin := (isMinimalRepresentative_adjacentMerge_iff F k hk (e' jj).val).mp (e' jj).property
    rw [h2] at hmin
    simp only [Fin.revPerm_apply, Fin.lt_def, Fin.val_rev] at hmin
    omega
  · let ι'' := T.normalizedJacquetMap (BlockShape.uniform m r hr) ι'
    refine ⟨ι'', normalizedJacquetMap_injective F T _ ι'
      (T.segmentInduced A.obj m hr).isSmooth hι', ?_⟩
    have hcomp : Q.comp ι'' = T.normalizedJacquetMap _ (q.comp ι') :=
      (BlockShape.normalizedJacquetOfMap_comp _ _ ι' q).symm
    have := hπirr
    rcases Representation.IsIrreducible.surjective_or_eq_zero (q.comp ι') with hsurj | hzero
    · left
      have hJ := normalizedJacquetMap_surjective F T (BlockShape.uniform m r hr) _
        ((T.normalizedProductInductionFunctor _).obj Y).isSmooth hsurj
      intro y
      obtain ⟨x, hx⟩ := hJ y
      exact ⟨x, (DFunLike.congr_fun hcomp x).trans hx⟩
    · right
      exact hcomp.trans ((congrArg (T.normalizedJacquetMap _) hzero).trans
        (normalizedJacquetMap_zero F T _))

end Langlands.SegmentFullJacquet
