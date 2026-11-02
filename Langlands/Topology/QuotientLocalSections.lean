import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions

/-! # Quotient models with continuous local sections -/

noncomputable section

universe u v

open Topology

namespace Langlands.Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every target point has an open neighborhood carrying a continuous section. -/
def HasContinuousLocalSections (f : X → Y) : Prop :=
  ∀ y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
    ∃ s : U → X, Continuous s ∧ ∀ z, f (s z) = z.val

theorem HasContinuousLocalSections.surjective {f : X → Y}
    (hs : HasContinuousLocalSections f) : Function.Surjective f := by
  intro y
  obtain ⟨U, _, hy, s, _, hsec⟩ := hs y
  exact ⟨s ⟨y, hy⟩, hsec ⟨y, hy⟩⟩

/-- Continuous local sections detect the target topology. -/
theorem HasContinuousLocalSections.isQuotientMap {f : X → Y}
    (hs : HasContinuousLocalSections f) (hf : Continuous f) :
    IsQuotientMap f := by
  refine ⟨isCoinducing_iff.mpr ?_, hs.surjective⟩
  intro W
  constructor
  · intro hW
    apply isOpen_iff_forall_mem_open.mpr
    intro y hy
    obtain ⟨U, hU, hyU, s, hcont, hsec⟩ := hs y
    refine ⟨Subtype.val '' (s ⁻¹' (f ⁻¹' W)), ?_, ?_, ?_⟩
    · rintro z ⟨t, ht, rfl⟩
      change f (s t) ∈ W at ht
      rwa [hsec t] at ht
    · exact hU.isOpenMap_subtype_val _ (hW.preimage hcont)
    · refine ⟨⟨y, hyU⟩, ?_, rfl⟩
      change f (s ⟨y, hyU⟩) ∈ W
      rwa [hsec]
  · exact fun hW => hW.preimage hf

/-- A continuous map with exactly the given fibers and continuous local sections
identifies the canonical quotient topology with the target topology. -/
def quotientHomeomorphOfLocalSections (r : Setoid X) (f : X → Y)
    (hf : Continuous f)
    (hfib : ∀ x x', r x x' ↔ f x = f x')
    (hs : HasContinuousLocalSections f) : Quotient r ≃ₜ Y := by
  let F : Quotient r → Y := Quotient.lift f (fun x x' h => (hfib x x').mp h)
  have hinj : Function.Injective F := by
    intro q q'
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h x' =>
        intro h
        exact Quotient.sound ((hfib x x').mpr h)
  have hsurj : Function.Surjective F :=
    Quotient.lift_surjective f _ hs.surjective
  let e : Quotient r ≃ Y := Equiv.ofBijective F ⟨hinj, hsurj⟩
  refine e.toHomeomorph fun W => ?_
  exact (isQuotientMap_quotient_mk'.isOpen_preimage (s := e ⁻¹' W)).symm.trans
    ((hs.isQuotientMap hf).isOpen_preimage (s := W))

@[simp] theorem quotientHomeomorphOfLocalSections_mk
    (r : Setoid X) (f : X → Y) (hf : Continuous f)
    (hfib : ∀ x x', r x x' ↔ f x = f x')
    (hs : HasContinuousLocalSections f) (x : X) :
    quotientHomeomorphOfLocalSections r f hf hfib hs ⟦x⟧ = f x := rfl

/-- A compact model with continuous local sections makes the canonical quotient compact. -/
theorem compactSpace_quotient_of_local_sections
    (r : Setoid X) (f : X → Y) (hf : Continuous f)
    (hfib : ∀ x x', r x x' ↔ f x = f x')
    (hs : HasContinuousLocalSections f) [CompactSpace Y] :
    CompactSpace (Quotient r) :=
  (quotientHomeomorphOfLocalSections r f hf hfib hs).symm.compactSpace

end Langlands.Topology
