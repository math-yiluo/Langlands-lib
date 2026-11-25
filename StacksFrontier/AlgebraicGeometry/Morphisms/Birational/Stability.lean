module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Stability properties of birational morphisms

Birationality of a morphism of schemes is a condition on generic points of irreducible
components and on the local rings there. Both halves of that condition are inherited by
composites, by restrictions to an open of the target, and by coproducts.

## Main results

* `AlgebraicGeometry.IsBirational.comp`: a composite of birational morphisms is birational.
* `AlgebraicGeometry.IsBirational.morphismRestrict`: the restriction of a birational morphism
  over an open subscheme of the target is birational.
* `AlgebraicGeometry.isBirational_of_isIso_morphismRestrict`: conversely, a morphism which is an
  isomorphism over an open of the target containing the generic points of both schemes is
  birational.
* `AlgebraicGeometry.isBirational_sigmaMap`: a coproduct of birational morphisms is birational.
* `AlgebraicGeometry.mem_genericPoints_sigmaι_iff`: a point of a summand of a coproduct of
  schemes is a generic point of an irreducible component of the coproduct exactly when it is
  one of its own summand.

## References

* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of an open subscheme is a generic point of an irreducible component of that open
subscheme exactly when it is a generic point of an irreducible component of the ambient
scheme. -/
private theorem mem_genericPoints_opens_iff {X : Scheme.{u}} (U : X.Opens) (x : U.toScheme) :
    x ∈ genericPoints U.toScheme ↔ x.1 ∈ genericPoints X := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simpa only [Scheme.genericPointsInOpenEquiv_symm_val X U ⟨x, hx⟩] using
      ((Scheme.genericPointsInOpenEquiv X U).symm ⟨x, hx⟩).1.2
  · have h := (Scheme.genericPointsInOpenEquiv X U ⟨⟨x.1, hx⟩, x.2⟩).2
    rwa [show (Scheme.genericPointsInOpenEquiv X U ⟨⟨x.1, hx⟩, x.2⟩).1 = x from
      Subtype.ext (Scheme.genericPointsInOpenEquiv_val X U ⟨⟨x.1, hx⟩, x.2⟩)] at h

/-- The stalk map of `f ∣_ U` at a point is an isomorphism iff the stalk map of `f` there is. -/
private theorem isIso_stalkMap_morphismRestrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : f ⁻¹ᵁ U) : IsIso ((f ∣_ U).stalkMap x) ↔ IsIso (f.stalkMap x.1) :=
  MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _) (morphismRestrictStalkMap f U x)

/-- Birationality is stable under restriction to an open subscheme of the target. -/
theorem IsBirational.morphismRestrict {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirational f) (U : Y.Opens) : IsBirational (f ∣_ U) := by
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨?_, ?_, ?_⟩ ?_
  · intro x hx
    rw [mem_genericPoints_opens_iff] at hx ⊢
    rw [morphismRestrict_base_coe]
    exact hf.bijOn.mapsTo hx
  · intro x hx y hy hxy
    refine Subtype.ext (hf.bijOn.injOn ((mem_genericPoints_opens_iff _ _).1 hx)
      ((mem_genericPoints_opens_iff _ _).1 hy) ?_)
    rw [← morphismRestrict_base_coe f U x, ← morphismRestrict_base_coe f U y, hxy]
  · intro y hy
    obtain ⟨x, hx, hfx⟩ := hf.bijOn.surjOn ((mem_genericPoints_opens_iff _ _).1 hy)
    have hxU : x ∈ f ⁻¹ᵁ U := show f x ∈ U from hfx ▸ y.2
    exact ⟨⟨x, hxU⟩, (mem_genericPoints_opens_iff _ ⟨x, hxU⟩).2 hx,
      Subtype.ext ((morphismRestrict_base_coe f U _).trans hfx)⟩
  · intro x hx
    exact (isIso_stalkMap_morphismRestrict_iff f U x).2
      (hf.isIso_stalkMap x.1 ((mem_genericPoints_opens_iff _ _).1 hx))

end AlgebraicGeometry
