import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Mathlib.CategoryTheory.MorphismProperty.Descent

/-! # Testing a represented relative property on an atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F G : Presheaf S} {f : F ⟶ G}

namespace RepresentedAtlas

variable (hr : IsRepresentableMorphism f) {U T : Over S}
    (a : (schemeYoneda S).obj U ⟶ G) (ha : IsEtale a)
    (g : (schemeYoneda S).obj T ⟶ G)

/-- The actual scheme over a test scheme representing its pullback of the atlas. -/
abbrev atlasScheme : Over S := ha.rep.pullback g

/-- The projection from the represented pullback of the map to the test scheme. -/
abbrev mapProjection : hr.pullback g ⟶ T := hr.snd g

/-- The projection from the represented pullback of the atlas to the test scheme. -/
abbrev atlasProjection : atlasScheme a ha g ⟶ T := ha.rep.snd g

/-- The pullback of the two represented projections gives a refinement on which
the map's source and the target atlas are both available. -/
abbrev refinement : Over S :=
  Limits.pullback (mapProjection hr g) (atlasProjection a ha g)

/-- The refinement maps to the source presheaf through the first represented projection. -/
abbrev refinementSource : (schemeYoneda S).obj (refinement hr a ha g) ⟶ F :=
  (schemeYoneda S).map (pullback.fst (mapProjection hr g) (atlasProjection a ha g)) ≫ hr.fst g

/-- The refinement maps to the represented pullback of the map along the atlas. -/
def comparison : refinement hr a ha g ⟶ hr.pullback a :=
  hr.lift (refinementSource hr a ha g)
    (pullback.snd (mapProjection hr g) (atlasProjection a ha g) ≫ ha.rep.fst' g) (by
      have h := (((IsPullback.of_hasPullback (mapProjection hr g)
        (atlasProjection a ha g)).map (schemeYoneda S)).paste_horiz (hr.isPullback g)).w
      have hw : (schemeYoneda S).map (atlasProjection a ha g) ≫ g =
          (schemeYoneda S).map (ha.rep.fst' g) ≫ a := (ha.rep.isPullback' g).w.symm
      simpa only [refinementSource, Functor.map_comp, Category.assoc, ← hw] using h)

set_option backward.isDefEq.respectTransparency false in
/-- Both ways to present the fibre product agree: the comparison square is a pullback. -/
theorem comparison_isPullback :
    IsPullback ((schemeYoneda S).map (comparison hr a ha g))
      ((schemeYoneda S).map
        (pullback.snd (mapProjection hr g) (atlasProjection a ha g)))
      ((schemeYoneda S).map (hr.snd a)) ((schemeYoneda S).map (ha.rep.fst' g)) := by
  let j := pullback.snd (mapProjection hr g) (atlasProjection a ha g)
  have houter : IsPullback (refinementSource hr a ha g)
      ((schemeYoneda S).map j) f ((schemeYoneda S).map (ha.rep.fst' g) ≫ a) := by
    have h := ((IsPullback.of_hasPullback (mapProjection hr g)
      (atlasProjection a ha g)).map (schemeYoneda S)).paste_horiz (hr.isPullback g)
    have hw : (schemeYoneda S).map (atlasProjection a ha g) ≫ g =
        (schemeYoneda S).map (ha.rep.fst' g) ≫ a := (ha.rep.isPullback' g).w.symm
    change IsPullback (refinementSource hr a ha g) ((schemeYoneda S).map j) f
      ((schemeYoneda S).map (atlasProjection a ha g) ≫ g) at h
    rwa [hw] at h
  apply IsPullback.of_right _ _ (hr.isPullback a)
  · dsimp only [comparison]
    rw [Functor.relativelyRepresentable.lift_fst]
    exact houter
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact (schemeYoneda S).congr_map (hr.lift_snd _ _ _)

end RepresentedAtlas

/-- A represented map has a scheme property once its pullback along one surjective
étale atlas has that property, provided the property is stable under base change
and descends along surjective étale scheme maps. Representability is retained
as an explicit premise. -/
theorem relativeProperty_of_etale_atlas
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})]
    (hr : IsRepresentableMorphism f) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ G) (ha : IsEtale a) (hs : IsSurjective a)
    (hP : P (hr.snd a).left) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) f := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply MorphismProperty.relative_of_snd hr
  intro T g
  let q := hr.snd g
  let p := ha.rep.snd g
  have hp : Etale p.left := ha.property_snd g
  have hps : Surjective p.left := hs.projection g (ha.rep.fst g) p (ha.rep.isPullback g)
  have h : P (pullback.snd q p).left :=
    MorphismProperty.of_isPullback
      ((isPullback_of_map (RepresentedAtlas.comparison_isPullback hr a ha g)).map
        (Over.forget S)) hP
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := P) (Q := @Etale.{u} ⊓ @Surjective.{u})
    ((IsPullback.of_hasPullback q p).map (Over.forget S)).flip ⟨hp, hps⟩ h

end Langlands.AlgebraicGeometry.AlgebraicSpace
