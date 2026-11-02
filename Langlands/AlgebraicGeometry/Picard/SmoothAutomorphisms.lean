import Langlands.AlgebraicGeometry.Picard.AutomorphismPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth scheme representations of actual relative automorphisms -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) (T : Over S)

/-- Every further relative test maps to the actual scheme carrying the bundle. -/
def sliceToBundleBase : Over T.left ⥤ Over ((relativeSpace f).obj T) :=
  T.iteratedSliceBackward ⋙ Over.post (relativeSpace f)

/-- Actual automorphisms of a bundle on a relative test, with the ordinary
pullback pseudofunctor's coherent restriction maps. -/
def sliceAutomorphismPresheaf (L : LineBundle ((relativeSpace f).obj T)) :
    AlgebraicSpace.Presheaf T.left :=
  ((sliceToBundleBase f T).op ⋙
    pseudofunctor.presheafHom (Core.mk L) (Core.mk L)) ⋙ uliftFunctor.{u + 1}

/-- Restricting relative global units to the slice gives the actual
scalar automorphisms on every further relative scheme test. -/
def sliceUnitsAutomorphismPresheafIso (L : LineBundle ((relativeSpace f).obj T)) :
    (Over.map T.hom).op ⋙ RelativeGlobalUnits.presheaf f ≅
      sliceAutomorphismPresheaf f T L :=
  (NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro Z W h
    rfl)) ≪≫
    isoWhiskerRight (isoWhiskerLeft (sliceToBundleBase f T).op
      (unitsAutomorphismPresheafIso L)) uliftFunctor.{u + 1}

/-- Every bundle on every relative test has a smooth scheme representing its
actual automorphism presheaf on the entire slice. -/
def HasSmoothAutomorphismSchemes : Prop :=
  ∀ (T : Over S) (L : LineBundle ((relativeSpace f).obj T)),
    ∃ G : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj G ≅
        sliceAutomorphismPresheaf f T L) ∧ Smooth G.hom

/-- Smooth representations of the relative-unit presheaf on all slices. -/
def HasSmoothUnitSchemes : Prop :=
  ∀ T : Over S, ∃ G : Over T.left,
    Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj G ≅
      (Over.map T.hom).op ⋙ RelativeGlobalUnits.presheaf f) ∧ Smooth G.hom

/-- A smooth unit scheme represents the automorphisms of every actual bundle. -/
lemma HasSmoothUnitSchemes.hasSmoothAutomorphismSchemes
    (h : HasSmoothUnitSchemes f) : HasSmoothAutomorphismSchemes f := by
  intro T L
  obtain ⟨G, ⟨e⟩, hG⟩ := h T
  exact ⟨G, ⟨e ≪≫ sliceUnitsAutomorphismPresheafIso f T L⟩, hG⟩

/-- The scalar comparison also recovers a smooth unit scheme from any bundle;
the trivial bundle makes the converse unconditional. -/
lemma hasSmoothAutomorphismSchemes_iff_hasSmoothUnitSchemes :
    HasSmoothAutomorphismSchemes f ↔ HasSmoothUnitSchemes f := by
  constructor
  · intro h T
    obtain ⟨G, ⟨e⟩, hG⟩ := h T (LineBundle.trivial _)
    exact ⟨G, ⟨e ≪≫ (sliceUnitsAutomorphismPresheafIso f T _).symm⟩, hG⟩
  · exact HasSmoothUnitSchemes.hasSmoothAutomorphismSchemes f

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
