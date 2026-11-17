import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Literal transport of sheaves through homeomorphisms across universes -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.HomeomorphTransport

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe uX uY uA vA vC uC vD uD

section Sites

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
variable [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
variable (A : Type uA) [Category.{vA} A]

/-- The usual sheaf equivalence needs only continuity of both inverse site
equivalences; its functors are literal precomposition. -/
def sheafEquivalence : Sheaf J A ≌ Sheaf K A where
  functor := e.inverse.sheafPushforwardContinuous A K J
  inverse := e.functor.sheafPushforwardContinuous A J K
  unitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.unitIso F.obj))
  counitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.counitIso F.obj))
  functor_unitIso_comp F := by
    ext
    simp [← Functor.map_comp, ← op_comp]

end Sites

variable {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
variable (e : X ≃ₜ Y)

/-- A homeomorphism identifies the actual open-set categories. -/
def opensEquivalence : Opens X ≌ Opens Y :=
  e.opensCongr.equivalence

/-- The open-set equivalence carries actual covering sieves to covering sieves. -/
theorem opensEquivalence_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      (opensEquivalence e).functor where
  cover_preserve {U S} hS := by
    intro y hy
    obtain ⟨V, f, hf, hyV⟩ := hS (e.symm y) hy
    exact ⟨(opensEquivalence e).functor.obj V, (opensEquivalence e).functor.map f,
      Sieve.image_mem_functorPushforward _ S hf, hyV⟩

/-- Literal open transport is continuous for the actual ordinary topologies. -/
theorem opensEquivalence_isContinuous :
    (opensEquivalence e).functor.IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (opensEquivalence_coverPreserving e)

variable (A : Type uA) [Category.{vA} A]

/-- Transport an actual sheaf through a homeomorphism without identifying the
space and coefficient universes. -/
def equivalence :
    TopCat.Sheaf A (TopCat.of X) ≌ TopCat.Sheaf A (TopCat.of Y) := by
  letI := opensEquivalence_isContinuous e
  haveI : (opensEquivalence e).inverse.IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    opensEquivalence_isContinuous e.symm
  exact sheafEquivalence (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    (opensEquivalence e) A

/-- The transported open sections are the original sections on the inverse-image open. -/
theorem equivalence_obj_obj (F : TopCat.Sheaf A (TopCat.of X)) (U : Opens Y) :
    ((equivalence e A).functor.obj F).obj.obj (op U) =
      F.obj.obj (op ((opensEquivalence e).inverse.obj U)) := rfl

/-- Transport to a larger universe along the canonical lift homeomorphism. -/
def uliftEquivalence :
    TopCat.Sheaf A (TopCat.of X) ≌
      TopCat.Sheaf A (TopCat.of (ULift.{uY} X)) :=
  equivalence Homeomorph.ulift.symm A

end Langlands.Sheaf.HomeomorphTransport
