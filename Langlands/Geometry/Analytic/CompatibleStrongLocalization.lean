import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Localization of actual original compatible strong atlas maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.CompatibleAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

set_option linter.checkUnivs false in
/-- The actual path-and-relations localization of the original compatible strong-map
category at its full affinoid-domain quasi-isomorphisms. -/
abbrev LocalizedCategory :=
  (quasiIsomorphisms (K := K) :
    MorphismProperty (CompatibleAtlasPresentation.{u, v, w} K)).Localization

/-- Send an original compatible presentation and its full bounded-map family
to the constructed quotient category. -/
def localizationFunctor :
    CompatibleAtlasPresentation.{u, v, w} K ⥤ LocalizedCategory.{u, v, w} (K := K) :=
  (quasiIsomorphisms (K := K)).Q

instance : (localizationFunctor (K := K)).IsLocalization (quasiIsomorphisms (K := K)) :=
  inferInstanceAs ((quasiIsomorphisms (K := K)).Q.IsLocalization _)

/-- The construction changes no object data: its objects are in bijection
with the original compatible presentations. -/
def localizedObjectEquiv :
    CompatibleAtlasPresentation.{u, v, w} K ≃ LocalizedCategory.{u, v, w} (K := K) :=
  Localization.Construction.objEquiv _

@[simp]
theorem localizedObjectEquiv_apply (A : CompatibleAtlasPresentation.{u, v, w} K) :
    localizedObjectEquiv A = localizationFunctor.obj A := rfl

variable {A B : CompatibleAtlasPresentation.{u, v, w} K}

/-- The constructed formal inverse makes each actual quasi-isomorphism
an isomorphism in the quotient. -/
def localizedQuasiIso (s : A ⟶ B) (hs : s.toStrongHom.IsQuasiIso) :
    localizationFunctor.obj A ≅ localizationFunctor.obj B :=
  Localization.isoOfHom localizationFunctor (quasiIsomorphisms (K := K)) s hs

@[simp]
theorem localizedQuasiIso_hom (s : A ⟶ B) (hs : s.toStrongHom.IsQuasiIso) :
    (localizedQuasiIso s hs).hom = localizationFunctor.map s := rfl

@[reassoc (attr := simp)]
theorem localizedQuasiIso_hom_inv_id (s : A ⟶ B) (hs : s.toStrongHom.IsQuasiIso) :
    localizationFunctor.map s ≫ (localizedQuasiIso s hs).inv = 𝟙 _ :=
  (localizedQuasiIso s hs).hom_inv_id

@[reassoc (attr := simp)]
theorem localizedQuasiIso_inv_hom_id (s : A ⟶ B) (hs : s.toStrongHom.IsQuasiIso) :
    (localizedQuasiIso s hs).inv ≫ localizationFunctor.map s = 𝟙 _ :=
  (localizedQuasiIso s hs).inv_hom_id

variable {D : Type*} [Category* D]

/-- Descend any functor which actually inverts the full quasi-isomorphisms. -/
def descend (F : CompatibleAtlasPresentation.{u, v, w} K ⥤ D)
    (hF : (quasiIsomorphisms (K := K)).IsInvertedBy F) :
    LocalizedCategory.{u, v, w} (K := K) ⥤ D :=
  Localization.Construction.lift F hF

@[simp]
theorem localizationFunctor_descend (F : CompatibleAtlasPresentation.{u, v, w} K ⥤ D)
    (hF : (quasiIsomorphisms (K := K)).IsInvertedBy F) :
    localizationFunctor ⋙ descend F hF = F :=
  Localization.Construction.fac F hF

/-- Strict factorization through this constructed model is unique. -/
theorem descend_unique (F : CompatibleAtlasPresentation.{u, v, w} K ⥤ D)
    (hF : (quasiIsomorphisms (K := K)).IsInvertedBy F)
    (G : LocalizedCategory.{u, v, w} (K := K) ⥤ D)
    (hG : localizationFunctor ⋙ G = F) : G = descend F hF :=
  Localization.Construction.uniq _ _ (hG.trans (localizationFunctor_descend F hF).symm)

/-- The universal property includes natural transformations, through
the equivalence with the full category of functors inverting quasi-isomorphisms. -/
def localizedFunctorEquivalence (D : Type*) [Category* D] :
    (LocalizedCategory.{u, v, w} (K := K) ⥤ D) ≌
      (quasiIsomorphisms (K := K)).FunctorsInverting D :=
  Localization.functorEquivalence localizationFunctor (quasiIsomorphisms (K := K)) D

/-- Every full quasi-isomorphism has its original ambient homeomorphism,
so the literal space functor inverts it in TopCat. -/
theorem spaceFunctor_inverts_quasiIsomorphisms :
    (quasiIsomorphisms (K := K) :
      MorphismProperty (CompatibleAtlasPresentation.{u, v, w} K)).IsInvertedBy spaceFunctor := by
  intro A B s hs
  exact (TopCat.isIso_iff_isHomeomorph (spaceFunctor.map s)).2 hs.1

/-- The underlying topological space functor on the constructed localization. -/
def localizedSpaceFunctor : LocalizedCategory.{u, v, w} (K := K) ⥤ TopCat.{v} :=
  descend spaceFunctor spaceFunctor_inverts_quasiIsomorphisms

@[simp]
theorem localizationFunctor_localizedSpaceFunctor :
    (localizationFunctor (K := K)) ⋙ localizedSpaceFunctor = spaceFunctor :=
  localizationFunctor_descend _ _

/-- The canonical natural comparison with the literal original space functor. -/
def localizedSpaceComparison :
    (localizationFunctor (K := K)) ⋙ localizedSpaceFunctor ≅ spaceFunctor :=
  eqToIso localizationFunctor_localizedSpaceFunctor

@[simp]
theorem localizedSpaceFunctor_obj (A : CompatibleAtlasPresentation.{u, v, w} K) :
    localizedSpaceFunctor.obj (localizationFunctor.obj A) = A.presentation.space := rfl

@[simp]
theorem localizedSpaceFunctor_map (f : A ⟶ B) :
    localizedSpaceFunctor.map (localizationFunctor.map f) = TopCat.ofHom f.baseMap := by
  exact Functor.congr_hom localizationFunctor_localizedSpaceFunctor f

@[simp]
theorem localizedSpaceComparison_hom_app (A : CompatibleAtlasPresentation.{u, v, w} K) :
    (localizedSpaceComparison (K := K)).hom.app A = 𝟙 A.presentation.space := by
  simp only [localizedSpaceComparison, eqToIso.hom, eqToHom_app]
  rfl

/-- The formal inverse acts on points by the inverse of the original
ambient homeomorphism, with its actual continuous topology. -/
theorem localizedSpaceFunctor_map_quasiIso_inv (s : A ⟶ B) (hs : s.toStrongHom.IsQuasiIso) :
    localizedSpaceFunctor.map (localizedQuasiIso s hs).inv =
      (TopCat.isoOfHomeo hs.1.homeomorph).inv := by
  have h : localizedSpaceFunctor.mapIso (localizedQuasiIso s hs) =
      TopCat.isoOfHomeo hs.1.homeomorph := by
    ext x
    exact congrArg (fun f => f x) (localizedSpaceFunctor_map s)
  exact congrArg Iso.inv h

/-- The descended space functor is the unique strict extension of the
literal spaces and continuous maps. -/
theorem localizedSpaceFunctor_unique
    (G : LocalizedCategory.{u, v, w} (K := K) ⥤ TopCat.{v})
    (hG : localizationFunctor ⋙ G = spaceFunctor) : G = localizedSpaceFunctor :=
  descend_unique _ _ G hG

end Langlands.Analytic.CompatibleAtlasPresentation
