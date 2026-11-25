module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourcePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Points and subschemes of fibres

For a composition `i ≫ f` the fibre of `i ≫ f` over a point `s` maps to the fibre of `f`
over `s`, compatibly with the two inclusions into the sources. This module builds that map,
shows that it inherits being an open or a closed immersion from `i`, and records how a point of
the source sits in the fibre over a point of the target described by an equation rather than by
`f x` itself.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberMapComp` is the induced morphism
  `(i ≫ f).fiber s ⟶ f.fiber s`.
* `AlgebraicGeometry.Scheme.Hom.asFiberAt` sends a point `x` of the source with `f x = y` to
  a point of `f.fiber y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.fiberMapComp_fiberι` is the compatibility of
  `fiberMapComp` with the inclusions of the fibres into the sources.
* `AlgebraicGeometry.genericPoints_preimage_of_isOpenImmersion` and
  `AlgebraicGeometry.genericPoints_preimage_of_isClosedImmersion` transport generic points of
  irreducible components backwards along an open, respectively closed, immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- Over the image point itself, `asFiberAt` is `asFiber`. -/
@[simp]
theorem asFiberAt_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    asFiberAt f x (f x) rfl = f.asFiber x := rfl

end Scheme.Hom

/-- A point of the source of an open immersion whose image is generic in an irreducible
component is itself generic in an irreducible component. -/
theorem genericPoints_preimage_of_isOpenImmersion {A B : Scheme.{u}} (j : A ⟶ B)
    [IsOpenImmersion j] {a : A} (ha : j a ∈ genericPoints B) : a ∈ genericPoints A := by
  have hpre : j ⁻¹' closure ({j a} : Set B) ∈ irreducibleComponents A :=
    preimage_mem_irreducibleComponents ha j.isOpenEmbedding
      ⟨j a, subset_closure (Set.mem_singleton _), ⟨a, rfl⟩⟩
  change closure ({a} : Set A) ∈ irreducibleComponents A
  rw [j.isOpenEmbedding.closure_eq_preimage_closure_image]
  simpa using hpre

/-- A point of the source of a closed immersion whose image is generic in an irreducible
component is itself generic in an irreducible component. -/
theorem genericPoints_preimage_of_isClosedImmersion {A B : Scheme.{u}} (j : A ⟶ B)
    [IsClosedImmersion j] {a : A} (hb : j a ∈ genericPoints B) : a ∈ genericPoints A := by
  have hclosure : j '' closure ({a} : Set A) = closure ({j a} : Set B) := by
    simpa only [Set.image_singleton] using
      (j.isClosedEmbedding.closure_image_eq ({a} : Set A)).symm
  have hpre : j ⁻¹' closure ({j a} : Set B) = closure ({a} : Set A) := by
    rw [← hclosure, Set.preimage_image_eq _ j.isClosedEmbedding.injective]
  have hCmax : Maximal IsIrreducible (closure ({j a} : Set B)) := hb
  refine ⟨isIrreducible_singleton.closure, fun E hE hDE x hx => ?_⟩
  have hCF : closure ({j a} : Set B) ⊆ closure (j '' E) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closure
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact subset_closure ⟨a, hDE (subset_closure (Set.mem_singleton a)), rfl⟩
  have hFC := hCmax.2 ((hE.image j j.continuous.continuousOn).closure) hCF
  rw [← hpre]
  exact hFC (subset_closure (show j x ∈ j '' E from ⟨x, hx, rfl⟩))

end AlgebraicGeometry

end
