module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Smoothness of a morphism at a point

A morphism of schemes is smooth at a point when its restriction to some open neighbourhood of
that point is smooth. This is equivalent to the morphism being given, near the point, by a smooth
homomorphism between the rings of sections of affine open neighbourhoods, and — over any
prescribed affine neighbourhood of the image — by a standard smooth one.

## Main definitions

* `InfinitesimalLifting.SmoothAt` expresses that a morphism of schemes is smooth at a specified
  point.

## Main results

* `InfinitesimalLifting.smoothAt_iff_exists_affine` characterizes smoothness at a point by affine
  neighbourhoods and the induced smooth ring homomorphism.
* `InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth` characterizes smoothness at a
  point by a standard smooth restriction over any prescribed affine neighbourhood of the image.
* `InfinitesimalLifting.smooth_iff_forall_smoothAt` and
  `InfinitesimalLifting.smooth_of_forall_smoothAt` globalize smoothness at every point to
  smoothness of the morphism.

## Implementation notes

The existing predicate `InfinitesimalLifting.SmoothAt` uses an arbitrary open neighbourhood on
which the restricted morphism is smooth. The two characterizations prove that this intrinsic form
is equivalent to the affine-open formulations, and their forward and reverse implications are the
introduction and elimination API for the affine witnesses.

Membership of the point in the inverse image of the chosen target open is the scheme-theoretic
expression of that open being a neighbourhood of its image, and the restricted morphism is
expressed by `AlgebraicGeometry.Scheme.Hom.resLE`.

The passage between a morphism restricted to an open subscheme and the map it induces on sections
is mediated by `AlgebraicGeometry.Scheme.Hom.resLE_appLE`. It is applied with its opens given
explicitly, so that the rewrite is a syntactic match rather than a definitional unfolding;
likewise the identification of the restriction of an inclusion with a presheaf restriction map is
isolated in `InfinitesimalLifting.isIso_ι_appLE`. This keeps both equivalences free of any
dependence on relaxed elaborator transparency.

The globalization goes through locality of smoothness on the source, which for a property coming
from a ring homomorphism property is
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`. That instance is supplied
explicitly rather than by inference: its ring homomorphism property is an instance-implicit
argument that instance resolution cannot determine from the goal alone.

## References

* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
* [Stacks Project, Tag 01V7](https://stacks.math.columbia.edu/tag/01V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace InfinitesimalLifting

/-- Smoothness at a point is equivalent to the existence of affine open neighbourhoods of the
point and of its image on whose rings of sections the induced homomorphism is smooth. -/
public theorem smoothAt_iff_exists_affine {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    InfinitesimalLifting.SmoothAt f x ↔
      ∃ (U : X.Opens) (V : S.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
        (_ : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V), (f.appLE V U hUV).hom.Smooth := by
  constructor
  · rintro ⟨W, hxW, hf⟩
    obtain ⟨V, hV, U, hU, hxU, hUV, -⟩ :=
      AlgebraicGeometry.Smooth.exists_isStandardSmooth (f.resLE ⊤ W le_top) ⟨x, hxW⟩
    have hs := (f.resLE ⊤ W le_top).smooth_appLE hV hU hUV
    rw [Scheme.Hom.resLE_appLE f (U := ⊤) (V := W) le_top V U hUV] at hs
    exact ⟨W.ι ''ᵁ U, (⊤ : S.Opens).ι ''ᵁ V, hU.image_of_isOpenImmersion _,
      hV.image_of_isOpenImmersion _, by simpa using W.mem_ι_image_iff.mpr hxU,
      (Scheme.Hom.le_resLE_preimage_iff f le_top V U).mp hUV, hs⟩
  · rintro ⟨U, V, hU, hV, hxU, hUV, hs⟩
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    have hg : Smooth (f.resLE V U hUV) :=
      (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
        ((RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f V U hUV)).mpr hs)
    refine ⟨U, hxU, ?_⟩
    rw [← f.resLE_map hUV le_top]
    infer_instance

end InfinitesimalLifting
