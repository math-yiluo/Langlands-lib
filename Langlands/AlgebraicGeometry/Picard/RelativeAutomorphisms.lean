import Langlands.AlgebraicGeometry.Picard.SmoothAutomorphisms
import Langlands.CategoryTheory.Sites.PresheafHomPrecomposition

/-! # Comparing the relative Picard automorphism presheaf -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) (T : Over S)

/-- Automorphisms formed directly with the actual relative pseudofunctor. -/
def relativeSliceAutomorphismPresheaf (L : LineBundle ((relativeSpace f).obj T)) :
    AlgebraicSpace.Presheaf T.left :=
  (T.iteratedSliceBackward.op ⋙
    (relative f).presheafHom (Core.mk L) (Core.mk L)) ⋙ uliftFunctor.{u + 1}

set_option backward.isDefEq.respectTransparency false in
/-- The direct relative and ordinary slice constructions agree naturally. -/
def sliceRelativeAutomorphismPresheafIso (L : LineBundle ((relativeSpace f).obj T)) :
    sliceAutomorphismPresheaf f T L ≅ relativeSliceAutomorphismPresheaf f T L :=
  isoWhiskerRight (isoWhiskerLeft T.iteratedSliceBackward.op
    (Langlands.CategoryTheory.presheafHomPrecompositionIso (relativeSpace f)
      pseudofunctor (Core.mk L) (Core.mk L)).symm) uliftFunctor.{u + 1}

/-- Relative global units are the automorphisms formed with the actual relative
pseudofunctor, naturally over the entire test slice. -/
def relativeSliceUnitsAutomorphismPresheafIso
    (L : LineBundle ((relativeSpace f).obj T)) :
    (Over.map T.hom).op ⋙ RelativeGlobalUnits.presheaf f ≅
      relativeSliceAutomorphismPresheaf f T L :=
  sliceUnitsAutomorphismPresheafIso f T L ≪≫
    sliceRelativeAutomorphismPresheafIso f T L

/-- Smooth scheme representations of the actual relative pseudofunctor's
automorphism presheaves over every test. -/
def HasSmoothRelativeAutomorphismSchemes : Prop :=
  ∀ (T : Over S) (L : LineBundle ((relativeSpace f).obj T)),
    ∃ G : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj G ≅
        relativeSliceAutomorphismPresheaf f T L) ∧ Smooth G.hom

/-- Smooth unit representatives give smooth representatives of actual relative
automorphisms. -/
lemma HasSmoothUnitSchemes.hasSmoothRelativeAutomorphismSchemes
    (h : HasSmoothUnitSchemes f) : HasSmoothRelativeAutomorphismSchemes f := by
  intro T L
  obtain ⟨G, ⟨e⟩, hG⟩ := h T
  exact ⟨G, ⟨e ≪≫ relativeSliceUnitsAutomorphismPresheafIso f T L⟩, hG⟩

/-- The actual relative condition is equivalent to smooth unit representation;
the trivial bundle supplies the converse on every test. -/
lemma hasSmoothRelativeAutomorphismSchemes_iff_hasSmoothUnitSchemes :
    HasSmoothRelativeAutomorphismSchemes f ↔ HasSmoothUnitSchemes f := by
  constructor
  · intro h T
    obtain ⟨G, ⟨e⟩, hG⟩ := h T (LineBundle.trivial _)
    exact ⟨G, ⟨e ≪≫ (relativeSliceUnitsAutomorphismPresheafIso f T _).symm⟩, hG⟩
  · exact HasSmoothUnitSchemes.hasSmoothRelativeAutomorphismSchemes f

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
