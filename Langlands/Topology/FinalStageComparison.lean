import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order

/-!
# Comparison of spaces with topologies defined by stages

A map between sets with final topologies is continuous if it has a continuous
lift from every source stage to some target stage. Such lifts in both directions
upgrade a set equivalence to a homeomorphism.
-/

noncomputable section

universe u v w z

namespace Langlands.Topology

variable {ι : Type u} {κ : Type v} {A : Type w} {B : Type z}
variable {P : ι → Type*} {Q : κ → Type*}
variable [∀ i, TopologicalSpace (P i)] [∀ j, TopologicalSpace (Q j)]

/-- Every source stage maps continuously into a target stage, compatibly with `f`. -/
def HasContinuousStageLifts (p : ∀ i, P i → A) (q : ∀ j, Q j → B) (f : A → B) : Prop :=
  ∀ i, ∃ (j : κ) (g : P i → Q j), Continuous g ∧ ∀ x, f (p i x) = q j (g x)

/-- Continuity follows by testing on all the stages of the final topology. -/
theorem HasContinuousStageLifts.continuous
    {p : ∀ i, P i → A} {q : ∀ j, Q j → B} {f : A → B}
    (h : HasContinuousStageLifts p q f) :
    @Continuous A B
      (⨆ i, TopologicalSpace.coinduced (p i) inferInstance)
      (⨆ j, TopologicalSpace.coinduced (q j) inferInstance) f := by
  let : TopologicalSpace B := ⨆ j, TopologicalSpace.coinduced (q j) inferInstance
  rw [continuous_iSup_dom]
  intro i
  rw [continuous_coinduced_dom]
  obtain ⟨j, g, hg, hcomm⟩ := h i
  have hq : @Continuous (Q j) B inferInstance
      (⨆ j, TopologicalSpace.coinduced (q j) inferInstance) (q j) :=
    continuous_iSup_rng (i := j) continuous_coinduced_rng
  have heq : f ∘ p i = q j ∘ g := funext hcomm
  rw [heq]
  exact hq.comp hg

/-- Compatible continuous stage lifts of an equivalence and its inverse give a
homeomorphism for the final topologies. -/
def homeomorphOfStageLifts
    (p : ∀ i, P i → A) (q : ∀ j, Q j → B) (e : A ≃ B)
    (h : HasContinuousStageLifts p q e)
    (h' : HasContinuousStageLifts q p e.symm) :
    @Homeomorph A B
      (⨆ i, TopologicalSpace.coinduced (p i) inferInstance)
      (⨆ j, TopologicalSpace.coinduced (q j) inferInstance) := by
  letI : TopologicalSpace A := ⨆ i, TopologicalSpace.coinduced (p i) inferInstance
  letI : TopologicalSpace B := ⨆ j, TopologicalSpace.coinduced (q j) inferInstance
  exact
    { toEquiv := e
      continuous_toFun := h.continuous
      continuous_invFun := h'.continuous }

@[simp]
theorem homeomorphOfStageLifts_apply
    (p : ∀ i, P i → A) (q : ∀ j, Q j → B) (e : A ≃ B)
    (h : HasContinuousStageLifts p q e)
    (h' : HasContinuousStageLifts q p e.symm) (x : A) :
    homeomorphOfStageLifts p q e h h' x = e x := rfl

end Langlands.Topology
