import Langlands.Topology.QuotientConnectedComponents
import Mathlib.Topology.Constructions

/-! # Component quotients from finite connected closed covers -/

noncomputable section

universe u v w z

open Topology

namespace Langlands.Topology

variable {A : Type u} {B : Type v} {ι : Type w}
  [TopologicalSpace A] [TopologicalSpace B]

/-- The map from the disjoint union of the members of a cover to its ambient space. -/
def coverSumMap (s : ι → Set A) : (Σ i, s i) → A :=
  fun x => x.2.val

/-- A finite closed cover presents the ambient space as a quotient of its disjoint union. -/
theorem isQuotientMap_coverSumMap [Finite ι]
    (s : ι → Set A) (hclosed : ∀ i, IsClosed (s i))
    (hcover : (⋃ i, s i) = Set.univ) :
    IsQuotientMap (coverSumMap s) := by
  have hc : Continuous (coverSumMap s) :=
    continuous_sigma fun _ => continuous_subtype_val
  have hs : Function.Surjective (coverSumMap s) := by
    intro x
    obtain ⟨i, hxi⟩ := Set.iUnion_eq_univ_iff.mp hcover x
    exact ⟨⟨i, ⟨x, hxi⟩⟩, rfl⟩
  have hcl : IsClosedMap (coverSumMap s) := by
    intro C hC
    have heq : coverSumMap s '' C =
        ⋃ i, (Subtype.val : s i → A) ''
          ((@Sigma.mk ι (fun j => ↥(s j)) i) ⁻¹' C) := by
      ext x
      constructor
      · rintro ⟨⟨i, y⟩, hy, rfl⟩
        exact Set.mem_iUnion.mpr ⟨i, y, hy, rfl⟩
      · intro hx
        obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
        exact ⟨⟨i, y⟩, hy, rfl⟩
    rw [heq]
    exact isClosed_iUnion_of_finite fun i =>
      (hclosed i).isClosedMap_subtype_val _ (hC.preimage continuous_sigmaMk)
  exact hcl.isQuotientMap hc hs

/-- Connected nonempty summands have precisely their summand indices as components. -/
def coverSumComponentsEquiv (s : ι → Set A) (hconn : ∀ i, IsConnected (s i)) :
    ConnectedComponents (Σ i, s i) ≃ ι := by
  classical
  letI : TopologicalSpace ι := ⊥
  letI : DiscreteTopology ι := ⟨rfl⟩
  have hc : Continuous (fun x : Σ i, s i => x.1) :=
    continuous_sigma fun _ => continuous_const
  let point (i : ι) : s i :=
    ⟨(hconn i).nonempty.some, (hconn i).nonempty.some_mem⟩
  refine
    { toFun := hc.connectedComponentsLift
      invFun := fun i => ConnectedComponents.mk ⟨i, point i⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    obtain ⟨⟨i, x⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (⟨i, point i⟩ : Σ j, s j) =
      ConnectedComponents.mk ⟨i, x⟩
    let : ConnectedSpace (s i) := isConnected_iff_connectedSpace.mp (hconn i)
    have he : ConnectedComponents.mk (point i) =
        ConnectedComponents.mk x := Subsingleton.elim _ _
    have hi : Continuous (@Sigma.mk ι (fun j => ↥(s j)) i) := continuous_sigmaMk
    simpa only [Continuous.connectedComponentsMap_mk] using
      congrArg hi.connectedComponentsMap he
  · intro i
    exact Continuous.connectedComponentsLift_apply_coe hc _

@[simp]
theorem coverSumComponentsEquiv_mk (s : ι → Set A)
    (hconn : ∀ i, IsConnected (s i)) (i : ι) (x : s i) :
    coverSumComponentsEquiv s hconn (ConnectedComponents.mk ⟨i, x⟩) = i := rfl

/-- The component space of a disjoint union of connected nonempty sets is discrete. -/
theorem discrete_coverSumComponents (s : ι → Set A)
    (hconn : ∀ i, IsConnected (s i)) :
    DiscreteTopology (ConnectedComponents (Σ i, s i)) := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  have hc : Continuous (coverSumComponentsEquiv s hconn) :=
    (continuous_sigma fun _ => continuous_const).connectedComponentsLift_continuous
  exact DiscreteTopology.of_continuous_injective hc
    (coverSumComponentsEquiv s hconn).injective

/-- Two members of a cover are incident if their images meet in the quotient. -/
def coverFibreRelation (f : A → B) (s : ι → Set A) (i j : ι) : Prop :=
  ∃ x ∈ s i, ∃ y ∈ s j, f x = f y

/-- A quotient and a finite connected closed cover compute its components by image incidence. -/
def closedCoverQuotientComponentsEquiv [Finite ι]
    (f : A → B) (hf : IsQuotientMap f)
    (s : ι → Set A) (hclosed : ∀ i, IsClosed (s i))
    (hconn : ∀ i, IsConnected (s i)) (hcover : (⋃ i, s i) = Set.univ) :
    Quot (coverFibreRelation f s) ≃ ConnectedComponents B := by
  letI := discrete_coverSumComponents s hconn
  let e := coverSumComponentsEquiv s hconn
  have he (c d : ConnectedComponents (Σ i, s i)) :
      componentFibreRelation (f ∘ coverSumMap s) c d ↔
        coverFibreRelation f s (e c) (e d) := by
    constructor
    · rintro ⟨⟨i, x⟩, ⟨j, y⟩, hx, hy, hxy⟩
      have hxi : i = e c := by
        simpa only [e, coverSumComponentsEquiv_mk] using congrArg e hx
      have hyj : j = e d := by
        simpa only [e, coverSumComponentsEquiv_mk] using congrArg e hy
      exact ⟨x, hxi ▸ x.property, y, hyj ▸ y.property, hxy⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      refine ⟨⟨e c, ⟨x, hx⟩⟩, ⟨e d, ⟨y, hy⟩⟩, ?_, ?_, hxy⟩
      · apply e.injective
        exact coverSumComponentsEquiv_mk s hconn _ _
      · apply e.injective
        exact coverSumComponentsEquiv_mk s hconn _ _
  exact (Quot.congr e he).symm.trans
    (quotientConnectedComponentsEquiv (f ∘ coverSumMap s)
      (hf.comp (isQuotientMap_coverSumMap s hclosed hcover)))

/-- Cardinalities of the finite image-incidence quotient give the actual component count. -/
theorem componentCount_eq_closedCoverIncidence [Finite ι]
    (f : A → B) (hf : IsQuotientMap f)
    (s : ι → Set A) (hclosed : ∀ i, IsClosed (s i))
    (hconn : ∀ i, IsConnected (s i)) (hcover : (⋃ i, s i) = Set.univ) :
    ENat.card (ConnectedComponents B) = ENat.card (Quot (coverFibreRelation f s)) :=
  (ENat.card_congr (closedCoverQuotientComponentsEquiv f hf s hclosed hconn hcover)).symm

end Langlands.Topology
