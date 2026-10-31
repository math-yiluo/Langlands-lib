import Langlands.Cohomology.DerivedPlusNaturality
import Langlands.Cohomology.DerivedComparison

/-! # Derived complexes along exact injective-preserving source functors -/

noncomputable section

namespace Langlands.Cohomology.DerivedPlusSource

open CategoryTheory CategoryTheory.Limits
open DerivedPlus

universe uC vC uD vD uE vE wC wD wE

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [EnoughInjectives D]
variable {E : Type uE} [Category.{vE} E] [Abelian E]
  [HasDerivedCategory.{wE} E]

section LocalizedHomology

/-- Localization of a bounded below complex preserves its cohomology. -/
def localizedHomologyIso (K : CochainComplex.Plus E) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor E n).obj (DerivedCategory.Plus.Q.obj K) ≅
      K.obj.homology n :=
  (DerivedCategory.homologyFunctor E n).mapIso
    ((DerivedCategory.Plus.QCompιIso E).app K) ≪≫
      (DerivedCategory.homologyFunctorFactors E n).app K.obj

omit [HasDerivedCategory C] [EnoughInjectives C]
  [HasDerivedCategory D] [EnoughInjectives D] in
set_option backward.isDefEq.respectTransparency false in
/-- The localization comparison respects every map of bounded below complexes. -/
@[reassoc]
theorem localizedHomologyIso_hom_naturality
    {K L : CochainComplex.Plus E} (φ : K ⟶ L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor E n).map (DerivedCategory.Plus.Q.map φ) ≫
        (localizedHomologyIso L n).hom =
      (localizedHomologyIso K n).hom ≫ HomologicalComplex.homologyMap φ.hom n := by
  have h := (DerivedCategory.Plus.QCompιIso E).hom.naturality φ
  simp only [Functor.comp_map] at h
  simp only [localizedHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  change (DerivedCategory.homologyFunctor E n).map _ ≫
    (DerivedCategory.homologyFunctor E n).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality]
  simp only [Category.assoc, ObjectProperty.ι_obj, ObjectProperty.ι_map]

end LocalizedHomology

section Image

variable (F : C ⥤ E) [F.Additive]

/-- Apply the functor to a natural-indexed resolution, then extend by zero. -/
def imageResolution {X : C} (I : InjectiveResolution X) : CochainComplex.Plus E :=
  ⟨((F.mapHomologicalComplex _).obj I.cocomplex).extend ComplexShape.embeddingUpNat,
    ⟨0, inferInstance⟩⟩

/-- Applying a functor before or after extension gives isomorphic complexes. -/
def imageResolutionComparison {X : C} (I : InjectiveResolution X) :
    F.mapCochainComplexPlus.obj (resolutionPlus I) ≅ imageResolution F I :=
  (CochainComplex.Plus.fullyFaithfulι E).preimageIso
    (mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).symm

/-- The extended image of any resolution represents the derived complex. -/
def imageResolutionIso {X : C} (I : InjectiveResolution X) :
    (derivedComplex F).obj X ≅ DerivedCategory.Plus.Q.obj (imageResolution F I) :=
  derivedComplexIso F I ≪≫ DerivedCategory.Plus.Q.mapIso (imageResolutionComparison F I)

/-- A compatible resolution map acts on the image resolution. -/
def imageResolutionMap {X Y : C} {f : X ⟶ Y}
    {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) : imageResolution F I ⟶ imageResolution F J :=
  ObjectProperty.homMk
    (HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map φ.hom)
      ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency false in
/-- The representative comparison is natural in every compatible resolution lift. -/
@[reassoc]
theorem imageResolutionIso_hom_naturality {X Y : C} {f : X ⟶ Y}
    {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    (derivedComplex F).map f ≫ (imageResolutionIso F J).hom =
      (imageResolutionIso F I).hom ≫
        DerivedCategory.Plus.Q.map (imageResolutionMap F φ) := by
  have h : F.mapCochainComplexPlus.map (resolutionPlusMap φ) ≫
      (imageResolutionComparison F J).hom =
      (imageResolutionComparison F I).hom ≫ imageResolutionMap F φ := by
    apply (CochainComplex.Plus.ι E).map_injective
    exact extendMapIso_hom_naturality ComplexShape.embeddingUpNat F φ.hom
  simp only [imageResolutionIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, derivedComplexIso_hom_naturality F φ]
  simp only [Category.assoc]
  rw [← Functor.map_comp, h, Functor.map_comp]

/-- The nonnegative cohomology of a localized image resolution is its
natural-indexed resolution cohomology. -/
def imageHomologyIso {X : C} (I : InjectiveResolution X) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor E q).obj
        (DerivedCategory.Plus.Q.obj (imageResolution F I)) ≅
      ((F.mapHomologicalComplex _).obj I.cocomplex).homology q :=
  localizedHomologyIso (imageResolution F I) q ≪≫
    ((F.mapHomologicalComplex _).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image-resolution comparisons give the previously published identification
with the ordinary right derived functor. -/
theorem imageHomologyIso_comp {X : C} (I : InjectiveResolution X) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor E q).map (imageResolutionIso F I).hom ≫
        (imageHomologyIso F I q).hom ≫ (I.isoRightDerivedObj F q).inv =
      (homologyIso F I q).hom := by
  have h := localizedHomologyIso_hom_naturality (imageResolutionComparison F I).hom
    (q : ℤ)
  simp only [imageResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    imageHomologyIso, Category.assoc]
  rw [reassoc_of% h]
  simp only [homologyIso, homologyResolutionIso, localizedHomologyIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  rfl

end Image

section Source

variable (F : C ⥤ E) [F.Additive] (T : C ⥤ D) [T.Additive]
  [T.PreservesHomology] [T.PreservesInjectiveObjects] (G : D ⥤ E) [G.Additive]
  (τ : F ⟶ T ⋙ G)

/-- A source functor maps every compatible resolution lift to a compatible lift. -/
def mapResolutionHom {X Y : C} {f : X ⟶ Y}
    {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    InjectiveResolution.Hom (DerivedComparison.mapInjectiveResolution T I)
      (DerivedComparison.mapInjectiveResolution T J) (T.map f) where
  hom := (T.mapHomologicalComplex _).map φ.hom
  ι_f_zero_comp_hom_f_zero := by
    rw [CochainComplex.single₀_map_f_zero]
    exact DerivedComparison.mapInjectiveResolution_comm T f I J φ.hom
      (φ.ι_f_zero_comp_hom_f_zero.trans (by rw [CochainComplex.single₀_map_f_zero]; rfl))

/-- The given square of functors acts degreewise on a resolution. -/
def resolutionSquare {X : C} (I : InjectiveResolution X) :
    (F.mapHomologicalComplex _).obj I.cocomplex ⟶
      (G.mapHomologicalComplex _).obj
        (DerivedComparison.mapInjectiveResolution T I).cocomplex :=
  (NatTrans.mapHomologicalComplex τ _).app I.cocomplex

/-- Extend the square of resolution complexes to integer cochain degrees. -/
def imageResolutionSquare {X : C} (I : InjectiveResolution X) :
    imageResolution F I ⟶
      imageResolution G (DerivedComparison.mapInjectiveResolution T I) :=
  ObjectProperty.homMk
    (HomologicalComplex.extendMap (resolutionSquare F T G τ I) ComplexShape.embeddingUpNat)

omit [HasDerivedCategory C] [EnoughInjectives C]
  [HasDerivedCategory D] [EnoughInjectives D] [HasDerivedCategory E] in
/-- The extended square is natural along compatible lifts. -/
@[reassoc]
theorem imageResolutionSquare_naturality {X Y : C} {f : X ⟶ Y}
    {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    imageResolutionMap F φ ≫ imageResolutionSquare F T G τ J =
      imageResolutionSquare F T G τ I ≫
        imageResolutionMap G (mapResolutionHom T φ) := by
  apply (CochainComplex.Plus.ι E).map_injective
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
    HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  exact congrArg (HomologicalComplex.extendMap · ComplexShape.embeddingUpNat)
    ((NatTrans.mapHomologicalComplex τ _).naturality φ.hom)

/-- The derived square computed with any specified resolution. -/
def derivedMapOfResolution {X : C} (I : InjectiveResolution X) :
    (derivedComplex F).obj X ⟶ (derivedComplex G).obj (T.obj X) :=
  (imageResolutionIso F I).hom ≫
    DerivedCategory.Plus.Q.map (imageResolutionSquare F T G τ I) ≫
      (imageResolutionIso G (DerivedComparison.mapInjectiveResolution T I)).inv

set_option backward.isDefEq.respectTransparency false in
/-- The derived square respects every compatible resolution lift. -/
@[reassoc]
theorem derivedMapOfResolution_naturality {X Y : C} {f : X ⟶ Y}
    {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    (derivedComplex F).map f ≫ derivedMapOfResolution F T G τ J =
      derivedMapOfResolution F T G τ I ≫ (derivedComplex G).map (T.map f) := by
  apply (cancel_mono
    (imageResolutionIso G (DerivedComparison.mapInjectiveResolution T J)).hom).1
  simp only [derivedMapOfResolution, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [imageResolutionIso_hom_naturality_assoc F φ,
    imageResolutionIso_hom_naturality G (mapResolutionHom T φ)]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, imageResolutionSquare_naturality, Functor.map_comp]

/-- The localized construction is independent of the injective resolution. -/
theorem derivedMapOfResolution_eq {X : C} (I J : InjectiveResolution X) :
    derivedMapOfResolution F T G τ I = derivedMapOfResolution F T G τ J := by
  have h := derivedMapOfResolution_naturality F T G τ (descHom (𝟙 X) I J)
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- A square of additive functors induces an actual natural transformation
of derived complexes along an exact source functor preserving injectives. -/
def derivedMap : derivedComplex F ⟶ T ⋙ derivedComplex G where
  app X := derivedMapOfResolution F T G τ (injectiveResolution X)
  naturality {X Y} f :=
    derivedMapOfResolution_naturality F T G τ
      (descHom f (injectiveResolution X) (injectiveResolution Y))

/-- Every resolution computes the component of the derived map. -/
theorem derivedMap_app {X : C} (I : InjectiveResolution X) :
    (derivedMap F T G τ).app X = derivedMapOfResolution F T G τ I :=
  derivedMapOfResolution_eq F T G τ _ I

omit [HasDerivedCategory C] [EnoughInjectives C]
  [HasDerivedCategory D] [EnoughInjectives D] in
set_option backward.isDefEq.respectTransparency false in
/-- The square on localized image resolutions induces the original
natural-indexed homology map. -/
@[reassoc]
theorem imageHomologyIso_square {X : C} (I : InjectiveResolution X) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor E q).map
        (DerivedCategory.Plus.Q.map (imageResolutionSquare F T G τ I)) ≫
        (imageHomologyIso G (DerivedComparison.mapInjectiveResolution T I) q).hom =
      (imageHomologyIso F I q).hom ≫
        HomologicalComplex.homologyMap (resolutionSquare F T G τ I) q := by
  have h := HomologicalComplex.extendHomologyIso_hom_naturality
    (resolutionSquare F T G τ I) ComplexShape.embeddingUpNat
    (j := q) (j' := (q : ℤ)) rfl
  simp only [imageHomologyIso, Iso.trans_hom]
  rw [localizedHomologyIso_hom_naturality_assoc]
  simpa only [Category.assoc, imageResolutionSquare, ObjectProperty.homMk] using
    congrArg ((localizedHomologyIso (imageResolution F I) q).hom ≫ ·) h

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary cohomology of the derived map is computed by the degreewise square
on any injective resolution. -/
theorem derivedMap_homology {X : C} (I : InjectiveResolution X) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor E q).map ((derivedMap F T G τ).app X) ≫
        (homologyIso G (DerivedComparison.mapInjectiveResolution T I) q).hom =
      (homologyIso F I q).hom ≫ (I.isoRightDerivedObj F q).hom ≫
        HomologicalComplex.homologyMap (resolutionSquare F T G τ I) q ≫
          ((DerivedComparison.mapInjectiveResolution T I).isoRightDerivedObj G q).inv := by
  rw [derivedMap_app F T G τ I,
    ← imageHomologyIso_comp G (DerivedComparison.mapInjectiveResolution T I) q,
    ← imageHomologyIso_comp F I q]
  have h : (DerivedCategory.Plus.homologyFunctor E q).map
      (imageResolutionIso G (DerivedComparison.mapInjectiveResolution T I)).inv ≫
      (DerivedCategory.Plus.homologyFunctor E q).map
        (imageResolutionIso G (DerivedComparison.mapInjectiveResolution T I)).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  simp only [derivedMapOfResolution, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  rw [imageHomologyIso_square_assoc]

end Source

end Langlands.Cohomology.DerivedPlusSource
