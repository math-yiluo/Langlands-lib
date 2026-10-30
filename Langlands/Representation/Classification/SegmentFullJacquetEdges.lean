import Langlands.Representation.Classification.SegmentFullJacquetAdjunction
import Langlands.Representation.Classification.SegmentEdgeJacquetStatement
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof

/-!
# Bookkeeping for the edge representations of a segment induction

Block permutations of the uniform shape, the separating scalars on Weyl
transports of the segment tensor with two adjacent factors swapped, and
exactness of the normalized Jacquet maps on injective and surjective
intertwiners.
-/

noncomputable section

namespace Langlands.SegmentFullJacquet

open GeneralLinear Geometric CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Minimal self-conjugating permutations of the uniform shape correspond to
permutations of its blocks. -/
def blockPermEquiv (m r : ℕ) (hr : 0 < r) :
    MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr) ≃ Equiv.Perm (Fin m) :=
  Equiv.ofBijective (blockPerm F) ⟨blockPerm_injective F, blockPerm_surjective F⟩

@[simp]
theorem blockPermEquiv_apply (m r : ℕ) (hr : 0 < r)
    (w : MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr)) :
    blockPermEquiv F m r hr w = blockPerm F w := rfl

@[simp]
theorem blockPerm_blockPermEquiv_symm (m r : ℕ) (hr : 0 < r) (g : Equiv.Perm (Fin m)) :
    blockPerm F ((blockPermEquiv F m r hr).symm g) = g :=
  (blockPermEquiv F m r hr).apply_symm_apply g

/-- The transposition of the adjacent blocks `k` and `k + 1`. -/
def adjacentSwap {m : ℕ} (k : ℕ) (hk : k + 1 < m) : Equiv.Perm (Fin m) :=
  Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩

/-- The separating scalar acts on the Weyl transport of the segment tensor with
its factors permuted by `e` through `segmentScalar` of `blockPerm w * e⁻¹`. -/
theorem transport_permuted_separatingScalar {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (ω : F.Carrierˣ →* ℂˣ)
    (hω : letI := T.topology
      Classification.HasScalarCharacter A.representation GeneralLinear.scalar ω)
    (e : Equiv.Perm (Fin m))
    (w : MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr)) :
    letI := T.topology
    ∀ v, transport _ _ w.val.val w.property
        (FiniteTensor.externalSmoothObject
          (fun i => T.segmentFactors A m hr (e i))).representation
        (separatingScalar F T m r hr) v =
      segmentScalar T ω r m ((blockPerm F w * e.symm : Equiv.Perm (Fin m)) : Fin m → Fin m) • v := by
  let := T.topology
  intro v
  refine (transport_blockTensor_blockScalarLevi w.val.val w.property
    (fun i => T.hasScalarCharacter_segmentFactor A (((e i : Fin m) : ℕ) : ℝ) hω) _ v).trans ?_
  congr 1
  unfold segmentScalar
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (blockPerm F w * e.symm : Equiv.Perm (Fin m)) (e i) = blockPerm F w i := by
    show blockPerm F w (e.symm (e i)) = blockPerm F w i
    exact congrArg (blockPerm F w) (e.symm_apply_apply i)
  exact congrArg (fun j => (((ω * (T.determinantPowerCharacter r (((e i : Fin m) : ℕ) : ℝ)).comp
    GeneralLinear.scalar) (separatingEntries T m j) : ℂˣ) : ℂ)) hi.symm

/-- Weyl transport of the segment tensor by a minimal self-conjugating
permutation `w` is equivalent to the segment tensor with its factors reordered by
the inverse block permutation. -/
theorem nonempty_transport_equiv_permuted {m r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (w : MinimalConjugatingPermutations (F := F.Carrier) (BlockShape.uniform m r hr)
      (BlockShape.uniform m r hr)) :
    letI := T.topology
    Nonempty ((transport _ _ w.val.val w.property
        (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation).Equiv
      (FiniteTensor.externalSmoothObject
        (fun i => T.segmentFactors A m hr ((blockPerm F w).symm i))).representation) := by
  let := T.topology
  have hidx : ∀ a, (blockIndex (BlockShape.uniform m r hr) (w.val.val a) : ℕ) =
      ((blockPerm F w).symm.symm (blockIndex (BlockShape.uniform m r hr) a) : ℕ) := by
    intro a
    rw [Equiv.symm_symm, TotalConjugatingCount.blockIndex_apply w.property a]
    rfl
  obtain ⟨-, hw⟩ := eq_blockPermutation_of_blockIndex (F := F.Carrier)
    (BlockShape.uniform m r hr) (blockPerm F w).symm w.val.val w.property w.val.property hidx
  have hconj := conjugatesLevi_blockPermutation (F := F.Carrier)
    (BlockShape.uniform m r hr) (blockPerm F w).symm
  have hcongr : ∀ (w' : Equiv.Perm (Fin (m * r)))
      (h1 : ConjugatesLevi (F := F.Carrier) (BlockShape.uniform m r hr)
        (BlockShape.uniform m r hr) w')
      (h2 : ConjugatesLevi (F := F.Carrier) (BlockShape.uniform m r hr)
        (BlockShape.uniform m r hr)
        ((BlockShape.uniform m r hr).blockPermutation (blockPerm F w).symm)),
      w' = (BlockShape.uniform m r hr).blockPermutation (blockPerm F w).symm →
      transport _ _ w' h1
          (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation =
        transport _ _ _ h2
          (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation := by
    rintro w' h1 h2 rfl
    rfl
  rw [hcongr w.val.val w.property hconj hw]
  exact ⟨blockPermutationTensorEquiv (F := F.Carrier) (BlockShape.uniform m r hr)
    (blockPerm F w).symm hconj (fun i => (T.segmentFactors A m hr i).representation)⟩

section Jacquet

variable {n : ℕ} (B : BlockShape n) {V W X : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

/-- The normalized Jacquet map of an injective intertwiner out of a smooth
target is injective. -/
theorem normalizedJacquetMap_injective
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (i : ρ.IntertwiningMap σ)
    (hσ : letI := T.topology
      IsSmooth σ) (hi : Function.Injective i) :
    Function.Injective (T.normalizedJacquetMap B i) := by
  let Q := LinearMap.range i.toLinearMap
  have hQ : ∀ g, Q ≤ Q.comap (σ g) := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨ρ g x, LinearMap.congr_fun (i.isIntertwining' g) x⟩
  let q : σ.IntertwiningMap (σ.quotient Q hQ) :=
    ⟨Q.mkQ, fun g => (Submodule.mapQ_mkQ Q Q (σ g) (h := hQ g)).symm⟩
  exact (T.normalizedJacquetMap_exact B i q hσ hi (Submodule.mkQ_surjective Q)
    (Submodule.ker_mkQ Q).symm).1

/-- The normalized Jacquet map of a surjective intertwiner out of a smooth
source is surjective. -/
theorem normalizedJacquetMap_surjective
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) X}
    (q : σ.IntertwiningMap τ)
    (hσ : letI := T.topology
      IsSmooth σ) (hq : Function.Surjective q) :
    Function.Surjective (T.normalizedJacquetMap B q) := by
  let i := CentralEigenspaceSplitting.subrepInclusion q.ker
  exact (T.normalizedJacquetMap_exact B i q hσ Subtype.val_injective hq
    (Submodule.range_subtype _)).2.2

/-- The normalized Jacquet map of the zero intertwiner is zero. -/
theorem normalizedJacquetMap_zero
    {σ : Representation ℂ (GeneralLinear n F.Carrier) W}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) X} :
    T.normalizedJacquetMap B (0 : σ.IntertwiningMap τ) = 0 := by
  apply Representation.IntertwiningMap.ext
  rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
  apply Representation.Coinvariants.hom_ext
  ext x
  rfl

end Jacquet

end Langlands.SegmentFullJacquet
