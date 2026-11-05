import Langlands.Geometry.Analytic.SaturatedSourceHomColimit
import Mathlib.CategoryTheory.EssentiallySmall

/-! # A category with the actual source-subatlas Hom quotients -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : SaturatedAtlasPresentation.{u, v, w} K}

/-- Identity in the explicit source-subatlas Hom model. -/
def sourceHomId (A : SaturatedAtlasPresentation.{u, v, w} K) : SourceHomQuotient A A :=
  sourceHomEquiv.symm (𝟙 (localizationFunctor.obj A))

/-- Composition transported through the proved actual localization comparison. -/
def sourceHomComp (f : SourceHomQuotient A B) (g : SourceHomQuotient B C) :
    SourceHomQuotient A C :=
  sourceHomEquiv.symm (sourceHomEquiv f ≫ sourceHomEquiv g)

@[simp]
theorem sourceHomEquiv_id (A : SaturatedAtlasPresentation.{u, v, w} K) :
    sourceHomEquiv (sourceHomId A) = 𝟙 (localizationFunctor.obj A) :=
  sourceHomEquiv.apply_symm_apply _

@[simp]
theorem sourceHomEquiv_comp (f : SourceHomQuotient A B) (g : SourceHomQuotient B C) :
    sourceHomEquiv (sourceHomComp f g) = sourceHomEquiv f ≫ sourceHomEquiv g :=
  sourceHomEquiv.apply_symm_apply _

@[simp]
theorem sourceHomId_comp (f : SourceHomQuotient A B) :
    sourceHomComp (sourceHomId A) f = f := by
  apply sourceHomEquiv.injective
  simp only [sourceHomEquiv_comp, sourceHomEquiv_id, Category.id_comp]

@[simp]
theorem sourceHomComp_id (f : SourceHomQuotient A B) :
    sourceHomComp f (sourceHomId B) = f := by
  apply sourceHomEquiv.injective
  simp only [sourceHomEquiv_comp, sourceHomEquiv_id, Category.comp_id]

theorem sourceHomComp_assoc (f : SourceHomQuotient A B) (g : SourceHomQuotient B C)
    (h : SourceHomQuotient C D) :
    sourceHomComp (sourceHomComp f g) h = sourceHomComp f (sourceHomComp g h) := by
  apply sourceHomEquiv.injective
  simp only [sourceHomEquiv_comp, Category.assoc]

/-- Any actual right fraction supplies a class by the constructed source normalization. -/
def sourceHomOfFraction (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    SourceHomQuotient A B :=
  sourceHomι (fractionSourceSelection φ) (fractionSourceReverse φ ≫ φ.f)

@[simp]
theorem sourceHomEquiv_ofFraction
    (φ : (quasiIsomorphisms (K := K)).RightFraction A B) :
    sourceHomEquiv (sourceHomOfFraction φ) = localizedRightFraction φ := by
  exact localizedRightFraction_sourceRefinedFraction φ

/-- Composition is represented by the actual Ore construction followed by source normalization. -/
theorem sourceHomComp_ι (P : A.presentation.atlas.RefiningSelection)
    (Q : B.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) (g : B.refiningSubpresentation Q ⟶ C) :
    sourceHomComp (sourceHomι P f) (sourceHomι Q g) =
      sourceHomOfFraction (rightFractionComp (sourceRefinementFraction P f)
        (sourceRefinementFraction Q g)) := by
  apply sourceHomEquiv.injective
  simp only [sourceHomEquiv_comp, sourceHomEquiv_ι, sourceHomEquiv_ofFraction,
    localizedRightFraction_comp]

set_option linter.checkUnivs false in
/-- The actual saturated presentations, with a separate category instance using source quotients. -/
def SourceCategory (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :=
  SaturatedAtlasPresentation.{u, v, w} K

namespace SourceCategory

/-- Retain all the original saturated atlas data as an object. -/
def ofPresentation (A : SaturatedAtlasPresentation.{u, v, w} K) :
    SourceCategory.{u, v, w} K := A

/-- Recover the literal saturated presentation, without changing any chart or algebra. -/
def toPresentation (X : SourceCategory.{u, v, w} K) :
    SaturatedAtlasPresentation.{u, v, w} K := X

@[simp]
theorem to_ofPresentation (A : SaturatedAtlasPresentation.{u, v, w} K) :
    (ofPresentation A).toPresentation = A := rfl

@[simp]
theorem of_toPresentation (X : SourceCategory.{u, v, w} K) :
    ofPresentation X.toPresentation = X := rfl

instance : Category.{max u v w} (SourceCategory.{u, v, w} K) where
  Hom X Y := SourceHomQuotient X.toPresentation Y.toPresentation
  id X := sourceHomId X.toPresentation
  comp f g := sourceHomComp f g
  id_comp := sourceHomId_comp
  comp_id := sourceHomComp_id
  assoc := sourceHomComp_assoc

/-- Compare the explicit Hom model with the already constructed path localization. -/
def comparisonFunctor :
    SourceCategory.{u, v, w} K ⥤ LocalizedCategory.{u, v, w} (K := K) where
  obj X := localizationFunctor.obj X.toPresentation
  map f := sourceHomEquiv f
  map_id X := sourceHomEquiv_id X.toPresentation
  map_comp f g := sourceHomEquiv_comp f g

instance : (comparisonFunctor (K := K) :
    SourceCategory.{u, v, w} K ⥤ _).Full where
  map_surjective := sourceHomEquiv.surjective

instance : (comparisonFunctor (K := K) :
    SourceCategory.{u, v, w} K ⥤ _).Faithful where
  map_injective := by
    intro X Y f g h
    exact (sourceHomEquiv (A := X.toPresentation) (B := Y.toPresentation)).injective h

theorem comparisonFunctor_obj_surjective :
    Function.Surjective (comparisonFunctor (K := K) :
      SourceCategory.{u, v, w} K ⥤ _).obj := by
  intro X
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  exact ⟨ofPresentation A, rfl⟩

instance : (comparisonFunctor (K := K) :
    SourceCategory.{u, v, w} K ⥤ _).EssSurj :=
  Functor.essSurj_of_surj comparisonFunctor_obj_surjective

instance : (comparisonFunctor (K := K) :
    SourceCategory.{u, v, w} K ⥤ _).IsEquivalence where

/-- A constructed equivalence; no category comparison is supplied as an input. -/
def localizationEquivalence :
    SourceCategory.{u, v, w} K ≌ LocalizedCategory.{u, v, w} (K := K) :=
  comparisonFunctor.asEquivalence

/-- Map an original complete strong morphism into the source quotient model. -/
def strongFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤ SourceCategory.{u, v, w} K where
  obj := ofPresentation
  map f := sourceHomEquiv.symm (localizationFunctor.map f)
  map_id A := by
    apply sourceHomEquiv.injective
    change sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map (𝟙 A))) =
      sourceHomEquiv (sourceHomId A)
    simp only [Equiv.apply_symm_apply, sourceHomEquiv_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply sourceHomEquiv.injective
    change sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map (f ≫ g))) =
      sourceHomEquiv (sourceHomComp (sourceHomEquiv.symm (localizationFunctor.map f))
        (sourceHomEquiv.symm (localizationFunctor.map g)))
    simp only [sourceHomEquiv_comp, Equiv.apply_symm_apply, CategoryTheory.Functor.map_comp]

@[simp]
theorem strongFunctor_comparisonFunctor :
    (strongFunctor (K := K) : SaturatedAtlasPresentation.{u, v, w} K ⥤ _) ⋙
      comparisonFunctor = localizationFunctor := by
  refine CategoryTheory.Functor.hext (F := strongFunctor ⋙ comparisonFunctor)
    (G := localizationFunctor) (fun _ => rfl) ?_
  intro A B f
  exact heq_of_eq (sourceHomEquiv.apply_symm_apply _)

/-- The inverse comparison identifies the original localization with the small Hom model. -/
def localizationFunctor_inverseComparison :
    localizationFunctor ⋙ (localizationEquivalence (K := K) :
      SourceCategory.{u, v, w} K ≌ _).inverse ≅ strongFunctor :=
  CategoryTheory.Functor.isoWhiskerRight (eqToIso strongFunctor_comparisonFunctor).symm
      localizationEquivalence.inverse ≪≫
    (CategoryTheory.Functor.associator strongFunctor comparisonFunctor
      localizationEquivalence.inverse) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft strongFunctor localizationEquivalence.unitIso.symm ≪≫
    strongFunctor.rightUnitor

instance : (strongFunctor (K := K) :
    SaturatedAtlasPresentation.{u, v, w} K ⥤ _).IsLocalization
      (quasiIsomorphisms (K := K)) :=
  CategoryTheory.Functor.IsLocalization.of_equivalence_target localizationFunctor
    (quasiIsomorphisms (K := K)) strongFunctor localizationEquivalence.symm
      localizationFunctor_inverseComparison

/-- Functors and natural transformations descend through the actual source-quotient category. -/
def functorEquivalence (D : Type*) [Category* D] :
    (SourceCategory.{u, v, w} K ⥤ D) ≌
      (quasiIsomorphisms (K := K)).FunctorsInverting D :=
  Localization.functorEquivalence strongFunctor (quasiIsomorphisms (K := K)) D

/-- Every source selection gives the same class for an original complete strong map. -/
theorem strongFunctor_map_eq_ι (P : A.presentation.atlas.RefiningSelection) (f : A ⟶ B) :
    strongFunctor.map f = sourceHomι P (A.refiningSubatlasInclusion P ≫ f) := by
  apply sourceHomEquiv.injective
  change sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map f)) =
    sourceHomEquiv (sourceHomι P (A.refiningSubatlasInclusion P ≫ f))
  rw [Equiv.apply_symm_apply, sourceHomEquiv_ι]
  change localizationFunctor.map f =
    (localizedQuasiIso (A.refiningSubatlasInclusion P)
      (isQuasiIso_refiningSubatlasInclusion P)).inv ≫
        localizationFunctor.map (A.refiningSubatlasInclusion P ≫ f)
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    localizedQuasiIso_inv_hom_id, Category.id_comp]

/-- The identity has the actual inclusion as numerator on every original-chart source. -/
theorem id_eq_ι (A : SaturatedAtlasPresentation.{u, v, w} K)
    (P : A.presentation.atlas.RefiningSelection) :
    𝟙 (ofPresentation A) = sourceHomι P (A.refiningSubatlasInclusion P) := by
  calc
    _ = strongFunctor.map (𝟙 A) := (strongFunctor.map_id A).symm
    _ = _ := by
      simpa only [Category.comp_id] using strongFunctor_map_eq_ι P (𝟙 A)

/-- The functor on the literal ambient topological spaces. -/
def spaceFunctor : SourceCategory.{u, v, w} K ⥤ TopCat.{v} :=
  comparisonFunctor ⋙ localizedSpaceFunctor

@[simp]
theorem spaceFunctor_obj (X : SourceCategory.{u, v, w} K) :
    spaceFunctor.obj X = X.toPresentation.presentation.space := rfl

/-- On a represented arrow, the space functor is exactly its continuous numerator. -/
@[simp]
theorem spaceFunctor_map_ι (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) :
    spaceFunctor.map (X := ofPresentation A) (Y := ofPresentation B) (sourceHomι P f) =
      TopCat.ofHom f.baseMap :=
  localizedSpaceFunctor_map_sourceHomEquiv_ι P f

/-- The original full strong maps retain their original continuous ambient maps. -/
@[simp]
theorem spaceFunctor_map_strong (f : A ⟶ B) :
    spaceFunctor.map (strongFunctor.map f) = TopCat.ofHom f.baseMap := by
  change localizedSpaceFunctor.map
    (sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map f))) = _
  rw [Equiv.apply_symm_apply, localizedSpaceFunctor_map]

@[simp]
theorem strongFunctor_spaceFunctor :
    (strongFunctor (K := K) : SaturatedAtlasPresentation.{u, v, w} K ⥤ _) ⋙ spaceFunctor =
      SaturatedAtlasPresentation.spaceFunctor := by
  change (strongFunctor ⋙ comparisonFunctor) ⋙ localizedSpaceFunctor = _
  rw [strongFunctor_comparisonFunctor, localizationFunctor_localizedSpaceFunctor]

end SourceCategory

/-- The actual path localization has small Homs at the explicit numerator universe. -/
instance localizedCategory_locallySmall :
    LocallySmall.{max u v w} (LocalizedCategory.{u, v, w} (K := K)) :=
  (locallySmall_congr (SourceCategory.localizationEquivalence (K := K))).1 inferInstance

end Langlands.Analytic.SaturatedAtlasPresentation
