import Langlands.AlgebraicGeometry.Modules.PushforwardComparison

/-! # Composite-functor comparison through a right resolution -/

noncomputable section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Langlands.Cohomology.AcyclicResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

section Augmentation

variable (F : C ⥤ D) [F.Additive]
  {A B : C} {K L : CochainComplex C ℕ}

/-- Apply an additive functor to an arbitrary augmentation. -/
def mapResolutionAugmentation (ε : (CochainComplex.single₀ C).obj A ⟶ K) :
    (CochainComplex.single₀ D).obj (F.obj A) ⟶ (F.mapHomologicalComplex _).obj K :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app A ≫
    (F.mapHomologicalComplex _).map ε

@[simp]
lemma mapResolutionAugmentation_f_zero
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) :
    (mapResolutionAugmentation F ε).f 0 = F.map (ε.f 0) := by
  simp only [mapResolutionAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, CochainComplex.single₀ObjXSelf,
    Iso.refl_hom, Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- Mapping the augmentation of an injective resolution agrees with the
published mapped injective-resolution augmentation. -/
@[simp]
lemma mapResolutionAugmentation_injectiveResolution (I : InjectiveResolution A) :
    mapResolutionAugmentation F I.ι = mapAugmentation F I := by
  ext
  simp only [mapResolutionAugmentation_f_zero, mapAugmentation_f_zero,
    CochainComplex.single₀ObjXSelf, Iso.refl_inv]
  erw [Category.id_comp]
  rfl

/-- Mapping augmentations preserves every commutative square over a map of objects. -/
@[reassoc]
lemma mapResolutionAugmentation_naturality
    (ε : (CochainComplex.single₀ C).obj A ⟶ K)
    (η : (CochainComplex.single₀ C).obj B ⟶ L)
    (a : A ⟶ B) (t : K ⟶ L)
    (ht : ε ≫ t = (CochainComplex.single₀ C).map a ≫ η) :
    mapResolutionAugmentation F ε ≫ (F.mapHomologicalComplex _).map t =
      (CochainComplex.single₀ D).map (F.map a) ≫ mapResolutionAugmentation F η := by
  simp only [mapResolutionAugmentation, Category.assoc]
  rw [← Functor.map_comp, ht, Functor.map_comp,
    ← Category.assoc]
  have hn := (HomologicalComplex.singleMapHomologicalComplex F
    (ComplexShape.up ℕ) 0).inv.naturality a
  simpa only [CategoryTheory.Functor.comp_map, Category.assoc] using
    congrArg (fun z => z ≫ (F.mapHomologicalComplex _).map η) hn.symm

end Augmentation

section Composite

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  (G : D ⥤ E) [G.Additive] {H : C ⥤ E} [H.Additive]
  (e : F ⋙ G ≅ H) {A : C} {K : CochainComplex C ℕ}
  (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]
  [QuasiIso (mapResolutionAugmentation F ε)]

/-- The published composite-functor comparison can be computed from any
right resolution whose image is again a right resolution. -/
@[reassoc]
theorem resolutionComparison_compComparison
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) (n : ℕ) :
    resolutionComparison H ε n ≫ compComparison G e A hA n =
      (HomologicalComplex.homologyFunctor E _ n).map
          ((Functor.mapHomologicalComplexCompIso e _).inv.app K) ≫
        resolutionComparison G (mapResolutionAugmentation F ε) n := by
  let I := injectiveResolution A
  let t := lift ε (𝟙 A) I.ι
  have ht : ε ≫ t = I.ι := comp_lift_id ε I
  have := quasiIso_mapAugmentation F I hA
  have hmap : mapResolutionAugmentation F ε ≫ (F.mapHomologicalComplex _).map t =
      mapAugmentation F I := by
    rw [mapResolutionAugmentation, Category.assoc, ← Functor.map_comp, ht]
    exact mapResolutionAugmentation_injectiveResolution F I
  have hc := resolutionComparison_naturality G (mapResolutionAugmentation F ε)
    (mapAugmentation F I) (𝟙 (F.obj A)) ((F.mapHomologicalComplex _).map t)
    (by simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hmap) n
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  have hn := (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.naturality t
  rw [resolutionComparison_eq H ε I t ht]
  simp only [comparison, compComparison, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  simp only [CategoryTheory.Functor.comp_map] at hc ⊢
  rw [← (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map_comp_assoc,
    hn, Functor.map_comp_assoc, CategoryTheory.Functor.comp_map, hc]

end Composite

end Langlands.Cohomology.AcyclicResolution
