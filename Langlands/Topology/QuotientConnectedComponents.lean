import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Logic.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-! # Connected components of a quotient with discrete source components -/

noncomputable section

universe u v w z

open Topology

namespace Langlands.Topology

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

/-- Two source components are joined when some fibre of the map meets both. -/
def componentFibreRelation (f : A → B) (c d : ConnectedComponents A) : Prop :=
  ∃ x y : A, ConnectedComponents.mk x = c ∧ ConnectedComponents.mk y = d ∧ f x = f y

/-- If the component space of the source is discrete, the components of a quotient
are exactly the source components modulo chains of identifications in map fibres. -/
def quotientConnectedComponentsEquiv (f : A → B) (hf : IsQuotientMap f)
    [DiscreteTopology (ConnectedComponents A)] :
    Quot (componentFibreRelation f) ≃ ConnectedComponents B := by
  classical
  let R := componentFibreRelation f
  let s := Function.surjInv hf.surjective
  have hs : ∀ y, f (s y) = y := Function.surjInv_eq hf.surjective
  let k : ConnectedComponents A → Quot R := Quot.mk R
  letI : TopologicalSpace (Quot R) := ⊥
  letI : DiscreteTopology (Quot R) := ⟨rfl⟩
  let g : B → Quot R := k ∘ ConnectedComponents.mk ∘ s
  have hgf : g ∘ f = k ∘ ConnectedComponents.mk := by
    funext x
    exact Quot.sound ⟨s (f x), x, rfl, rfl, hs (f x)⟩
  have hg : Continuous g := hf.continuous_iff.mpr (by
    rw [hgf]
    exact continuous_of_discreteTopology.comp ConnectedComponents.continuous_coe)
  let forward : Quot R → ConnectedComponents B :=
    Quot.lift hf.continuous.connectedComponentsMap (by
      rintro c d ⟨x, y, hx, hy, hxy⟩
      rw [← hx, ← hy, Continuous.connectedComponentsMap_mk,
        Continuous.connectedComponentsMap_mk, hxy])
  refine
    { toFun := forward
      invFun := hg.connectedComponentsLift
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    induction q using Quot.ind with
    | _ c =>
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      change hg.connectedComponentsLift (.mk (f x)) = k (.mk x)
      rw [Continuous.connectedComponentsLift_apply_coe]
      exact congrFun hgf x
  · intro c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    change forward (g y) = ConnectedComponents.mk y
    change hf.continuous.connectedComponentsMap (.mk (s y)) = .mk y
    rw [Continuous.connectedComponentsMap_mk, hs y]

/-- The component count of such a quotient is determined by the source component
set and the fibre-incidence relation on it. -/
theorem componentCount_eq_of_fibreRelationEquiv
    {C : Type w} {D : Type z} [TopologicalSpace C] [TopologicalSpace D]
    (f : A → B) (g : C → D) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    [DiscreteTopology (ConnectedComponents A)] [DiscreteTopology (ConnectedComponents C)]
    (e : ConnectedComponents A ≃ ConnectedComponents C)
    (he : ∀ c d, componentFibreRelation f c d ↔ componentFibreRelation g (e c) (e d)) :
    ENat.card (ConnectedComponents B) = ENat.card (ConnectedComponents D) :=
  ENat.card_congr
    ((quotientConnectedComponentsEquiv f hf).symm.trans
      ((Quot.congr e he).trans (quotientConnectedComponentsEquiv g hg)))

end Langlands.Topology
