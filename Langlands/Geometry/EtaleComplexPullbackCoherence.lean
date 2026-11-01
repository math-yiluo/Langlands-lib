import Langlands.Geometry.EtaleSectionPullbackCoherence

/-! # Identity and composition for actual bounded-below geometric pullback -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]

/-- The actual geometric identity comparison applied to bounded-below complexes. -/
def inverseImageComplexId (X : Scheme.{u}) :
    (inverseImage (𝟙 X) R).mapCochainComplexPlus ≅
      𝟭 (CochainComplex.Plus (ModuleSheaf X R)) :=
  NatIso.ofComponents
    (fun K => (CochainComplex.Plus.ι (ModuleSheaf X R)).preimageIso
      (((NatIso.mapHomologicalComplex (inverseImageId R X) (.up ℤ)) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleSheaf X R) (.up ℤ)).app K.obj))
    (fun {_K _L} a => by
      apply (CochainComplex.Plus.ι (ModuleSheaf X R)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (((NatIso.mapHomologicalComplex (inverseImageId R X) (.up ℤ)) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleSheaf X R) (.up ℤ)).hom.naturality a.hom))

/-- Its component in each degree is the original geometric identity comparison. -/
@[simp] theorem inverseImageComplexId_hom_f (X : Scheme.{u})
    (K : CochainComplex.Plus (ModuleSheaf X R)) (i : ℤ) :
    ((inverseImageComplexId R X).hom.app K).hom.f i =
      (inverseImageId R X).hom.app (K.obj.X i) := by
  change (((CochainComplex.Plus.ι (ModuleSheaf X R)).map
    ((inverseImageComplexId R X).hom.app K)).f i) = _
  dsimp only [inverseImageComplexId, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.preimageIso_hom]
  rw [Functor.map_preimage]
  simp

/-- The actual geometric composition comparison applied termwise to
bounded-below complexes. -/
def inverseImageComplexComp (f : Z ⟶ X) (g : V ⟶ Z) :
    (inverseImage f R).mapCochainComplexPlus ⋙
        (inverseImage g R).mapCochainComplexPlus ≅
      (inverseImage (g ≫ f) R).mapCochainComplexPlus :=
  NatIso.ofComponents
    (fun K => (CochainComplex.Plus.ι (ModuleSheaf V R)).preimageIso
      ((Functor.mapHomologicalComplexCompIso (inverseImageComp R f g) (.up ℤ)).app K.obj))
    (fun {_K _L} a => by
      apply (CochainComplex.Plus.ι (ModuleSheaf V R)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (Functor.mapHomologicalComplexCompIso
        (inverseImageComp R f g) (.up ℤ)).hom.naturality a.hom)

/-- Its component in each degree is the original geometric composition comparison. -/
@[simp] theorem inverseImageComplexComp_hom_f (f : Z ⟶ X) (g : V ⟶ Z)
    (K : CochainComplex.Plus (ModuleSheaf X R)) (i : ℤ) :
    ((inverseImageComplexComp R f g).hom.app K).hom.f i =
      (inverseImageComp R f g).hom.app (K.obj.X i) := by
  change (((CochainComplex.Plus.ι (ModuleSheaf V R)).map
    ((inverseImageComplexComp R f g).hom.app K)).f i) = _
  dsimp only [inverseImageComplexComp, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.preimageIso_hom]
  rw [Functor.map_preimage]
  rfl

end Langlands.Geometry.EtaleInverseImage

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]

/-- Actual section-complex pullback along the identity respects the
constructed coefficient-complex identification. -/
@[reassoc] theorem sectionsComplexPullback_id
    (K : CochainComplex.Plus (ModuleSheaf X R)) :
    (sectionsComplexPullback (𝟙 X) R).app K ≫
        (sections X R).mapCochainComplexPlus.map
          ((inverseImageComplexId R X).hom.app K) = 𝟙 _ := by
  apply (CochainComplex.Plus.ι (ModuleCat.{u} R)).map_injective
  apply HomologicalComplex.hom_ext
  intro i
  change ((sectionsComplexPullback (𝟙 X) R).app K).hom.f i ≫
    (sections X R).map (((inverseImageComplexId R X).hom.app K).hom.f i) = 𝟙 _
  rw [sectionsComplexPullback_app_f, inverseImageComplexId_hom_f]
  exact sectionsPullback_id R (K.obj.X i)

/-- Actual section-complex pullback respects composition with its constructed
coefficient-complex comparison. -/
@[reassoc] theorem sectionsComplexPullback_comp (f : Z ⟶ X) (g : V ⟶ Z)
    (K : CochainComplex.Plus (ModuleSheaf X R)) :
    (sectionsComplexPullback f R).app K ≫
        (sectionsComplexPullback g R).app ((inverseImage f R).mapCochainComplexPlus.obj K) ≫
        (sections V R).mapCochainComplexPlus.map
          ((inverseImageComplexComp R f g).hom.app K) =
      (sectionsComplexPullback (g ≫ f) R).app K := by
  apply (CochainComplex.Plus.ι (ModuleCat.{u} R)).map_injective
  apply HomologicalComplex.hom_ext
  intro i
  change ((sectionsComplexPullback f R).app K).hom.f i ≫
    ((sectionsComplexPullback g R).app
      ((inverseImage f R).mapCochainComplexPlus.obj K)).hom.f i ≫
    (sections V R).map (((inverseImageComplexComp R f g).hom.app K).hom.f i) =
    ((sectionsComplexPullback (g ≫ f) R).app K).hom.f i
  simp only [sectionsComplexPullback_app_f, inverseImageComplexComp_hom_f]
  exact sectionsPullback_comp R f g (K.obj.X i)

/-- Successive actual pullbacks of section complexes as a natural transformation. -/
def compositeSectionsComplexPullback (f : Z ⟶ X) (g : V ⟶ Z) :
    (sections X R).mapCochainComplexPlus ⟶
      ((inverseImage f R).mapCochainComplexPlus ⋙
        (inverseImage g R).mapCochainComplexPlus) ⋙
          (sections V R).mapCochainComplexPlus :=
  sectionsComplexPullback f R ≫
    Functor.whiskerLeft (inverseImage f R).mapCochainComplexPlus
      (sectionsComplexPullback g R) ≫
    (Functor.associator _ _ _).inv

/-- The successive section-complex map is the constructed map for the composite. -/
theorem compositeSectionsComplexPullback_eq (f : Z ⟶ X) (g : V ⟶ Z) :
    compositeSectionsComplexPullback R f g ≫
        Functor.whiskerRight (inverseImageComplexComp R f g).hom
          (sections V R).mapCochainComplexPlus =
      sectionsComplexPullback (g ≫ f) R := by
  apply NatTrans.ext
  funext K
  simpa [compositeSectionsComplexPullback] using sectionsComplexPullback_comp R f g K

end Langlands.Geometry.EtaleDerivedGlobalPullback
