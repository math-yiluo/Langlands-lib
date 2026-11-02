import Langlands.GroupScheme.Rational.StandardParabolic
import Mathlib.LinearAlgebra.Reflection

/-!
# Relative reflections

An element `w` of the relative Weyl group `N(k)/Z(k)` is a reflection in the relative root `α`
when its action on the `ℚ`-span of the relative roots is a reflection sending `1 ⊗ α` to its
negative. The relative reflections of a set `J` of relative roots, and in particular the simple
relative reflections attached to a cocharacter, are the candidate generators of the relative
Weyl group used by the reductive Tits-system targets. That each simple root has exactly one
reflection is a structural assertion, not part of these definitions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom]

/-- `w` is a reflection in the relative root `α`: `α` is a relative root, and the action of `w`
on `relativeRootSpan i` is the reflection `y ↦ y - f y • (1 ⊗ α)` for a linear form `f` with
`f (1 ⊗ α) = 2`. -/
def IsRelativeReflection (α : characterLattice T) (w : relativeWeylGroup i) : Prop :=
  ∃ hα : α ∈ relativeRoots i, ∃ f : Module.Dual ℚ (relativeRootSpan i),
    ∃ h : f ⟨toRat α, toRat_mem_ratSpan hα⟩ = 2, relativeWeylAction i w = Module.reflection h

/-- The relative reflections in the roots of a set `J` of characters. -/
def relativeReflections (J : Set (characterLattice T)) : Set (relativeWeylGroup i) :=
  {w | ∃ α ∈ J, IsRelativeReflection i α w}

/-- The simple relative reflections: the reflections in the simple relative roots of `ν`. -/
abbrev simpleRelativeReflections (ν : cocharacterLattice T) : Set (relativeWeylGroup i) :=
  relativeReflections i (simpleRelativeRoots i ν)

variable {i}

theorem mem_relativeReflections {J : Set (characterLattice T)} {w : relativeWeylGroup i} :
    w ∈ relativeReflections i J ↔ ∃ α ∈ J, IsRelativeReflection i α w :=
  Iff.rfl

theorem IsRelativeReflection.mem_relativeRoots {α : characterLattice T}
    {w : relativeWeylGroup i} (h : IsRelativeReflection i α w) : α ∈ relativeRoots i :=
  h.1

/-- A reflection in `α` sends `1 ⊗ α` to its negative. -/
theorem IsRelativeReflection.relativeWeylAction_apply_self {α : characterLattice T}
    {w : relativeWeylGroup i} (h : IsRelativeReflection i α w) :
    relativeWeylAction i w ⟨toRat α, toRat_mem_ratSpan h.1⟩ =
      -⟨toRat α, toRat_mem_ratSpan h.1⟩ := by
  obtain ⟨hα, f, hf, hw⟩ := h
  exact (DFunLike.congr_fun hw _).trans (Module.reflection_apply_self hf)

theorem relativeReflections_mono {J K : Set (characterLattice T)} (hJK : J ⊆ K) :
    relativeReflections i J ⊆ relativeReflections i K :=
  fun _ ⟨α, hα, h⟩ => ⟨α, hJK hα, h⟩

@[simp]
theorem relativeReflections_empty : relativeReflections i (∅ : Set (characterLattice T)) = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, hα, _⟩ => hα

theorem relativeReflections_subset_simple {ν : cocharacterLattice T}
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) :
    relativeReflections i J ⊆ simpleRelativeReflections i ν :=
  relativeReflections_mono hJ

/-- Rank zero: without simple relative roots there are no simple relative reflections. -/
theorem simpleRelativeReflections_eq_empty {ν : cocharacterLattice T}
    (h : simpleRelativeRoots i ν = ∅) : simpleRelativeReflections i ν = ∅ := by
  rw [simpleRelativeReflections, h, relativeReflections_empty]

end Langlands.GroupScheme
