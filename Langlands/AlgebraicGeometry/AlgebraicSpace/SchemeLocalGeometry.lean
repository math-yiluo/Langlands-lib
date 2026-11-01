import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Affine representation and scheme-local morphism properties

Affineness refers to the actual representing scheme. Finite and open-immersion
properties are tested on every represented scheme pullback.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Representation by an actual scheme whose underlying scheme is affine. -/
def IsRepresentedByAffineScheme (X : AlgebraicSpace S) : Prop :=
  ∃ U : Over S, _root_.AlgebraicGeometry.IsAffine U.left ∧
    Nonempty ((schemeYoneda S).obj U ≅ X.presheaf)

/-- An affine scheme representation is in particular a scheme representation. -/
theorem IsRepresentedByAffineScheme.representedByScheme {X : AlgebraicSpace S}
    (hX : IsRepresentedByAffineScheme X) : IsRepresentedByScheme X := by
  obtain ⟨U, _, hU⟩ := hX
  exact ⟨U, hU⟩

/-- An actual affine scheme included as a space is represented by that affine scheme. -/
theorem schemeToSpace_isRepresentedByAffineScheme (U : Over S)
    [_root_.AlgebraicGeometry.IsAffine U.left] :
    IsRepresentedByAffineScheme ((schemeToSpace S).obj U) :=
  ⟨U, inferInstance, ⟨Iso.refl _⟩⟩

variable {F G : Presheaf S} {f : F ⟶ G}

/-- A representable transformation whose every represented projection is finite. -/
def IsFinite (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
    (Over.forget S)).relative (schemeYoneda S) f

/-- A representable transformation whose every represented projection is an open immersion. -/
def IsOpenImmersion (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
    (Over.forget S)).relative (schemeYoneda S) f

/-- Finite transformations are representable by actual schemes. -/
theorem IsFinite.representable (hf : IsFinite f) : IsRepresentableMorphism f :=
  hf.1

/-- Every projection in a represented square of a finite map is a finite scheme morphism. -/
theorem IsFinite.projection (hf : IsFinite f) {U V : Over S}
    (g : (schemeYoneda S).obj U ⟶ G) (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) :
    _root_.AlgebraicGeometry.IsFinite p.left :=
  hf.2 g a p h

/-- The chosen represented projection of any representability witness is finite. -/
theorem IsFinite.pullback_finite (hf : IsFinite f) (hr : IsRepresentableMorphism f)
    {U : Over S} (g : (schemeYoneda S).obj U ⟶ G) :
    _root_.AlgebraicGeometry.IsFinite (hr.snd g).left :=
  hf.projection g (hr.fst g) (hr.snd g) (hr.isPullback g)

/-- Open immersions are representable by actual schemes. -/
theorem IsOpenImmersion.representable (hf : IsOpenImmersion f) :
    IsRepresentableMorphism f :=
  hf.1

/-- Every projection in a represented square of an open immersion is a scheme open immersion. -/
theorem IsOpenImmersion.projection (hf : IsOpenImmersion f) {U V : Over S}
    (g : (schemeYoneda S).obj U ⟶ G) (a : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ U)
    (h : IsPullback a ((schemeYoneda S).map p) f g) :
    _root_.AlgebraicGeometry.IsOpenImmersion p.left :=
  hf.2 g a p h

/-- The chosen represented projection of any representability witness is an open immersion. -/
theorem IsOpenImmersion.pullback_openImmersion (hf : IsOpenImmersion f)
    (hr : IsRepresentableMorphism f) {U : Over S} (g : (schemeYoneda S).obj U ⟶ G) :
    _root_.AlgebraicGeometry.IsOpenImmersion (hr.snd g).left :=
  hf.projection g (hr.fst g) (hr.snd g) (hr.isPullback g)

/-- A representable closed immersion is finite, with no order or nilpotence assumption. -/
theorem IsClosedImmersion.finite (hf : IsClosedImmersion f) : IsFinite f := by
  apply MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S))
    (P' := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (Over.forget S)) (F := schemeYoneda S) ?_ f hf
  intro U V p hp
  let : _root_.AlgebraicGeometry.IsClosedImmersion p.left := hp
  exact inferInstanceAs (_root_.AlgebraicGeometry.IsFinite p.left)

/-- Every unrestricted thickening is finite. -/
theorem IsThickening.finite (hf : IsThickening f) : IsFinite f :=
  hf.closedImmersion.finite

end Langlands.AlgebraicGeometry.AlgebraicSpace
