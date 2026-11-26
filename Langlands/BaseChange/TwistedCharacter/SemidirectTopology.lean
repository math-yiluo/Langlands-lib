import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Regular

/-! # Product coordinates on a semidirect product with discrete component group -/

namespace SemidirectProduct

open Set Topology

variable {G C : Type*} [Group G] [Group C] (φ : C →* MulAut G)
  [TopologicalSpace G] [TopologicalSpace C]

/-- The topology of the two underlying coordinates of a semidirect product. -/
scoped instance productTopology : TopologicalSpace (G ⋊[φ] C) :=
  .induced (equivProd (φ := φ)) inferInstance

/-- The two coordinates as a homeomorphism. -/
def homeomorphProd : (G ⋊[φ] C) ≃ₜ G × C :=
  (equivProd (φ := φ)).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp]
theorem homeomorphProd_apply (x : G ⋊[φ] C) :
    homeomorphProd φ x = (x.left, x.right) := rfl

scoped instance [T2Space G] [T2Space C] : T2Space (G ⋊[φ] C) :=
  (homeomorphProd φ).symm.t2Space

scoped instance [LocallyCompactSpace G] [LocallyCompactSpace C] :
    LocallyCompactSpace (G ⋊[φ] C) :=
  (homeomorphProd φ).locallyCompactSpace_iff.mpr inferInstance

scoped instance [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace C] :
    TotallyDisconnectedSpace (G ⋊[φ] C) :=
  (homeomorphProd φ).symm.totallyDisconnectedSpace

theorem continuous_left : Continuous (fun x : G ⋊[φ] C => x.left) :=
  continuous_fst.comp (homeomorphProd φ).continuous

theorem continuous_right : Continuous (fun x : G ⋊[φ] C => x.right) :=
  continuous_snd.comp (homeomorphProd φ).continuous

variable [DiscreteTopology C]

/-- A coordinate slice at a discrete index is an open embedding. -/
theorem isOpenEmbedding_slice (c : C) :
    IsOpenEmbedding (fun g : G => (⟨g, c⟩ : G ⋊[φ] C)) := by
  change IsOpenEmbedding ((homeomorphProd φ).symm ∘ fun g : G => (g, c))
  apply (homeomorphProd φ).symm.isOpenEmbedding.comp
  refine ⟨isEmbedding_prodMkLeft c, ?_⟩
  have hrange : range (fun g : G => (g, c)) = univ ×ˢ {c} := by
    ext p
    simp [Prod.ext_iff, eq_comm]
  rw [hrange]
  exact isOpen_univ.prod (isOpen_discrete _)

/-- The canonical subgroup at the identity of the index group is open. -/
theorem isOpenEmbedding_inl : IsOpenEmbedding (inl (φ := φ) : G → G ⋊[φ] C) :=
  isOpenEmbedding_slice φ 1

/-- A discrete group acting by continuous automorphisms gives a topological semidirect
product in the coordinate topology. -/
theorem isTopologicalGroup_of_continuous [IsTopologicalGroup G]
    (hφ : ∀ c, Continuous (φ c)) : IsTopologicalGroup (G ⋊[φ] C) where
  continuous_mul := by
    have ha : Continuous (fun p : C × G => φ p.1 p.2) :=
      continuous_prod_of_discrete_left.mpr hφ
    have hc : Continuous (fun p : C × C => p.1 * p.2) := continuous_of_discreteTopology
    change Continuous ((homeomorphProd φ).symm ∘ fun p : (G ⋊[φ] C) × (G ⋊[φ] C) =>
      (p.1.left * φ p.1.right p.2.left, p.1.right * p.2.right))
    refine (homeomorphProd φ).symm.continuous.comp (Continuous.prodMk ?_ ?_)
    · exact ((continuous_left φ).comp continuous_fst).mul
        (ha.comp (((continuous_right φ).comp continuous_fst).prodMk
          ((continuous_left φ).comp continuous_snd)))
    · exact hc.comp (((continuous_right φ).comp continuous_fst).prodMk
        ((continuous_right φ).comp continuous_snd))
  continuous_inv := by
    have ha : Continuous (fun p : C × G => φ p.1 p.2) :=
      continuous_prod_of_discrete_left.mpr hφ
    have hc : Continuous (fun c : C => c⁻¹) := continuous_of_discreteTopology
    change Continuous ((homeomorphProd φ).symm ∘ fun p : G ⋊[φ] C =>
      (φ p.right⁻¹ p.left⁻¹, p.right⁻¹))
    exact (homeomorphProd φ).symm.continuous.comp
      ((ha.comp ((hc.comp (continuous_right φ)).prodMk (continuous_left φ).inv)).prodMk
        (hc.comp (continuous_right φ)))

end SemidirectProduct
