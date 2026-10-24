import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Geometric.RefinementDefinitions

/-! Actual flattened product coordinates for the common refined Levi. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Reindex the flattened product by the actual nested block coordinates. -/
def flattenedLeviProductEquiv : (B.flatten S).Levi R ≃* (∀ i, (S i).Levi R) :=
  MulEquiv.symm
    { toEquiv := (Equiv.piCurry (fun i j => GeneralLinear ((S i).size j) R)).symm.trans
        (Equiv.piCongrLeft'
          (fun q : (i : Fin B.length) × Fin (S i).length =>
            GeneralLinear ((S q.1).size q.2) R) (B.flattenBlockEquiv S))
      map_mul' := fun _ _ => rfl }

@[simp] theorem flattenedLeviProductEquiv_symm_apply
    (m : ∀ i, (S i).Levi R) (k : Fin (B.flatten S).length) :
    (flattenedLeviProductEquiv R B S).symm m k =
      m ((B.flattenBlockEquiv S).symm k).1 ((B.flattenBlockEquiv S).symm k).2 := rfl

@[simp] theorem flattenedLeviProductEquiv_apply_symm
    (m : (B.flatten S).Levi R) (k : Fin (B.flatten S).length) :
    flattenedLeviProductEquiv R B S m
      ((B.flattenBlockEquiv S).symm k).1 ((B.flattenBlockEquiv S).symm k).2 = m k :=
  congrFun ((flattenedLeviProductEquiv R B S).symm_apply_apply m) k

/-- At the block numbered by `(i,j)`, transport the matrix size by the proved
flattened-size equality. -/
theorem flattenedLeviProductEquiv_apply (m : (B.flatten S).Levi R)
    (i : Fin B.length) (j : Fin (S i).length) :
    flattenedLeviProductEquiv R B S m i j =
      reindex (finCongr (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩))
        (m (B.flattenBlockEquiv S ⟨i, j⟩)) := by
  have key : ∀ (k : Fin (B.flatten S).length)
      (q : (i : Fin B.length) × Fin (S i).length)
      (h : (B.flattenBlockEquiv S).symm k = q),
      flattenedLeviProductEquiv R B S m q.1 q.2 =
        reindex (finCongr (congrArg
          (fun r : (i : Fin B.length) × Fin (S i).length => (S r.1).size r.2) h))
          (m k) := by
    intro k q h
    subst q
    rw [flattenedLeviProductEquiv_apply_symm]
    rfl
  exact key _ ⟨i, j⟩ ((B.flattenBlockEquiv S).symm_apply_apply ⟨i, j⟩)

/-- The actual flattened product Levi identified with the existing refined subgroup. -/
def flattenedLeviEquiv : (B.flatten S).Levi R ≃* refinedLevi R B S :=
  (flattenedLeviProductEquiv R B S).trans (refinedLeviEquiv R B S)

/-- Forward inner-block formula, with the actual size transport. -/
theorem flattenedLeviEquiv_component (m : (B.flatten S).Levi R)
    (i : Fin B.length) (j : Fin (S i).length) :
    (refinedLeviEquiv R B S).symm (flattenedLeviEquiv R B S m) i j =
      reindex (finCongr (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩))
        (m (B.flattenBlockEquiv S ⟨i, j⟩)) := by
  simp only [flattenedLeviEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact flattenedLeviProductEquiv_apply R B S m i j

/-- Inverse inner-block formula, using the inverse size transport. -/
theorem flattenedLeviEquiv_symm_component (m : refinedLevi R B S)
    (i : Fin B.length) (j : Fin (S i).length) :
    (flattenedLeviEquiv R B S).symm m (B.flattenBlockEquiv S ⟨i, j⟩) =
      (reindex (finCongr (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩))).symm
        ((refinedLeviEquiv R B S).symm m i j) := by
  apply (reindex (finCongr (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩))).injective
  rw [MulEquiv.apply_symm_apply, ← flattenedLeviEquiv_component,
    MulEquiv.apply_symm_apply]

private theorem nestedLeviEmbedding_apply_ne (m : ∀ i, (S i).Levi R)
    (q q' : (i : Fin B.length) × Fin (S i).length) (hq : q ≠ q')
    (a : Fin ((S q.1).size q.2)) (b : Fin ((S q'.1).size q'.2)) :
    B.leviEmbedding R (fun i => (S i).leviEmbedding R (m i))
      (B.index q.1 ((S q.1).index q.2 a))
      (B.index q'.1 ((S q'.1).index q'.2 b)) = 0 := by
  rcases q with ⟨i, j⟩
  rcases q' with ⟨i', j'⟩
  by_cases hi : i = i'
  · subst i'
    rw [B.leviEmbedding_apply_same]
    exact (S i).leviEmbedding_apply_ne R (m i) a b (fun h => hq (by cases h; rfl))
  · exact B.leviEmbedding_apply_ne R _ _ _ hi

/-- Nested block-diagonal inclusion is exactly inclusion of the flattened blocks. -/
theorem flattenedLeviEquiv_embedding (m : (B.flatten S).Levi R) :
    B.leviEmbedding R (flattenedLeviEquiv R B S m).val =
      (B.flatten S).leviEmbedding R m := by
  change B.leviEmbedding R
    (fun i => (S i).leviEmbedding R (flattenedLeviProductEquiv R B S m i)) = _
  apply Units.ext
  ext x y
  obtain ⟨⟨k, a⟩, rfl⟩ := (B.flatten S).indexEquiv.surjective x
  obtain ⟨⟨l, b⟩, rfl⟩ := (B.flatten S).indexEquiv.surjective y
  change B.leviEmbedding R _ ((B.flatten S).index k a) ((B.flatten S).index l b) =
    (B.flatten S).leviEmbedding R m ((B.flatten S).index k a) ((B.flatten S).index l b)
  by_cases h : k = l
  · subst l
    rw [(B.flatten S).leviEmbedding_apply_same, B.flatten_index S k a,
      B.flatten_index S k b, B.leviEmbedding_apply_same]
    exact ((S ((B.flattenBlockEquiv S).symm k).1).leviEmbedding_apply_same R _
      ((B.flattenBlockEquiv S).symm k).2 a b).trans
      (congrArg (fun g : GeneralLinear ((B.flatten S).size k) R => g a b)
        (flattenedLeviProductEquiv_apply_symm R B S m k))
  · rw [(B.flatten S).leviEmbedding_apply_ne R m a b h,
      B.flatten_index S k a, B.flatten_index S l b]
    exact nestedLeviEmbedding_apply_ne R B S _ _ _
      (fun e => h ((B.flattenBlockEquiv S).symm.injective e)) a b

/-- The inverse equivalence has the same ambient matrix. -/
theorem flattenedLeviEquiv_symm_embedding (m : refinedLevi R B S) :
    (B.flatten S).leviEmbedding R ((flattenedLeviEquiv R B S).symm m) =
      B.leviEmbedding R m.val := by
  rw [← flattenedLeviEquiv_embedding, MulEquiv.apply_symm_apply]

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The product reindexing respects the product topologies. -/
def flattenedLeviProductEquivContinuous : (B.flatten S).Levi R ≃ₜ* (∀ i, (S i).Levi R) where
  toMulEquiv := flattenedLeviProductEquiv R B S
  continuous_toFun := by
    change Continuous (fun m : (B.flatten S).Levi R => flattenedLeviProductEquiv R B S m)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous (fun m => flattenedLeviProductEquiv R B S m i j)
    simp_rw [flattenedLeviProductEquiv_apply]
    exact (reindexContinuous (R := R)
      (finCongr (B.flatten_size_flattenBlockEquiv S ⟨i, j⟩))).continuous.comp
      (continuous_apply _)
  continuous_invFun := by
    change Continuous (fun m : ∀ i, (S i).Levi R => (flattenedLeviProductEquiv R B S).symm m)
    exact continuous_pi fun k =>
      (continuous_apply ((B.flattenBlockEquiv S).symm k).2).comp
        (continuous_apply ((B.flattenBlockEquiv S).symm k).1)

/-- Continuous multiplicative equivalence to the actual refined subgroup. -/
def flattenedLeviEquivContinuous : (B.flatten S).Levi R ≃ₜ* refinedLevi R B S :=
  (flattenedLeviProductEquivContinuous R B S).trans (refinedLeviEquivContinuous R B S)

end Topology
end Langlands.Geometric
