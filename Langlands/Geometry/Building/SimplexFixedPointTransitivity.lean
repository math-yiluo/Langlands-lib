import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fintype.Sets
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# A unique fixed point in a finite simplex forces vertex transitivity

The acting group need not be finite. The affine maps need only extend its action
on the vertices.
-/

noncomputable section

namespace Langlands.Geometry.Building

variable {Γ I V : Type*} [Group Γ] [Fintype I] [MulAction Γ I]
  [AddCommGroup V] [Module ℝ V]

/-- The common fixed points of the supplied affine maps in the closed simplex
spanned by `p` form a subsingleton. -/
def SimplexFixedPointSubsingleton (p : I → V) (ρ : Γ → V →ᵃ[ℝ] V) : Prop :=
  Set.Subsingleton {x : V | x ∈ convexHull ℝ (Set.range p) ∧ ∀ γ, ρ γ x = x}

private def vertexOrbit (Γ : Type*) [Group Γ] {I : Type*} [Fintype I]
    [MulAction Γ I] (i : I) : Finset I := by
  classical
  exact (MulAction.orbit Γ i).toFinset

private theorem mem_vertexOrbit (i j : I) :
    j ∈ vertexOrbit Γ i ↔ ∃ γ : Γ, γ • i = j := by
  classical
  simp [vertexOrbit, MulAction.mem_orbit_iff]

private theorem vertexOrbit_nonempty (i : I) : (vertexOrbit Γ i).Nonempty :=
  ⟨i, (mem_vertexOrbit i i).2 ⟨1, one_smul Γ i⟩⟩

private theorem vertexOrbit_map (γ : Γ) (i : I) :
    (vertexOrbit Γ i).map (MulAction.toPerm γ).toEmbedding = vertexOrbit Γ i := by
  classical
  ext j
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨k, hk, hkj⟩
    change γ • k = j at hkj
    obtain ⟨δ, rfl⟩ := (mem_vertexOrbit i k).1 hk
    exact (mem_vertexOrbit i j).2 ⟨γ * δ, by simpa [mul_smul] using hkj⟩
  · intro hj
    refine ⟨γ⁻¹ • j, ?_, ?_⟩
    · obtain ⟨δ, rfl⟩ := (mem_vertexOrbit i j).1 hj
      exact (mem_vertexOrbit i _).2 ⟨γ⁻¹ * δ, mul_smul _ _ _⟩
    · exact smul_inv_smul γ j

private theorem vertexOrbit_centroid_fixed (p : I → V) (ρ : Γ → V →ᵃ[ℝ] V)
    (heq : ∀ γ i, ρ γ (p i) = p (γ • i)) (i : I) (γ : Γ) :
    ρ γ ((vertexOrbit Γ i).centroid ℝ p) = (vertexOrbit Γ i).centroid ℝ p := by
  classical
  have hw := (vertexOrbit Γ i).sum_centroidWeights_eq_one_of_nonempty ℝ
    (vertexOrbit_nonempty i)
  rw [Finset.centroid_def, (vertexOrbit Γ i).map_affineCombination p _ hw]
  have hp : ρ γ ∘ p = p ∘ MulAction.toPerm γ := by
    funext j
    exact heq γ j
  rw [hp]
  change (vertexOrbit Γ i).centroid ℝ (p ∘ MulAction.toPerm γ) =
    (vertexOrbit Γ i).centroid ℝ p
  simpa only [Equiv.coe_toEmbedding, vertexOrbit_map] using
    (Finset.centroid_map ℝ (vertexOrbit Γ i) (MulAction.toPerm γ).toEmbedding p).symm

private theorem vertexOrbit_centroid_mem (p : I → V) (i : I) :
    (vertexOrbit Γ i).centroid ℝ p ∈ convexHull ℝ (Set.range p) := by
  apply affineCombination_mem_convexHull
  · intro j hj
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact (vertexOrbit Γ i).sum_centroidWeights_eq_one_of_nonempty ℝ
      (vertexOrbit_nonempty i)

/-- If a finite affinely independent vertex family is equivariant for affine
maps extending a group action, and its closed simplex contains at most one
common fixed point, then the group acts transitively on the vertices. -/
theorem exists_smul_eq_of_simplexFixedPointSubsingleton
    (p : I → V) (hp : AffineIndependent ℝ p) (ρ : Γ → V →ᵃ[ℝ] V)
    (heq : ∀ γ i, ρ γ (p i) = p (γ • i))
    (hfix : SimplexFixedPointSubsingleton p ρ) (i j : I) :
    ∃ γ : Γ, γ • i = j := by
  classical
  have hcent : (vertexOrbit Γ i).centroid ℝ p = (vertexOrbit Γ j).centroid ℝ p :=
    hfix ⟨vertexOrbit_centroid_mem p i, vertexOrbit_centroid_fixed p ρ heq i⟩
      ⟨vertexOrbit_centroid_mem p j, vertexOrbit_centroid_fixed p ρ heq j⟩
  have hweights := hp.indicator_eq_of_affineCombination_eq
    (vertexOrbit Γ i) (vertexOrbit Γ j)
    ((vertexOrbit Γ i).centroidWeights ℝ) ((vertexOrbit Γ j).centroidWeights ℝ)
    ((vertexOrbit Γ i).sum_centroidWeights_eq_one_of_nonempty ℝ (vertexOrbit_nonempty i))
    ((vertexOrbit Γ j).sum_centroidWeights_eq_one_of_nonempty ℝ (vertexOrbit_nonempty j))
    hcent
  have hj : j ∈ vertexOrbit Γ j := (mem_vertexOrbit j j).2 ⟨1, one_smul Γ j⟩
  by_contra hn
  have hnj : j ∉ vertexOrbit Γ i := fun h => hn ((mem_vertexOrbit i j).1 h)
  have hzero : (0 : ℝ) = ((vertexOrbit Γ j).card : ℝ)⁻¹ := by
    simpa [Set.indicator_of_notMem hnj, Set.indicator_of_mem hj] using congrFun hweights j
  have hcard : ((vertexOrbit Γ j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (vertexOrbit_nonempty j))
  exact (inv_ne_zero hcard) hzero.symm

end Langlands.Geometry.Building
