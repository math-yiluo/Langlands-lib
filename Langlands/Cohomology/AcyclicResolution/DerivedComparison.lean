import Langlands.Cohomology.AcyclicResolution.Comparison
import Langlands.Cohomology.DerivedPlusNaturality
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Derived comparison of right resolutions

The map from an arbitrary right resolution to the right derived complex, with
its independence, naturality, and agreement with the degreewise comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Langlands.Cohomology.AcyclicResolution

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- Apply `F` to the integer extension of a natural-indexed complex and pass to
its actual derived category. -/
def derivedResolutionFunctor : CochainComplex C ℕ ⥤ DerivedCategory D :=
  ComplexShape.embeddingUpNat.extendFunctor C ⋙
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- Homotopic maps induce the same map under `derivedResolutionFunctor`. -/
lemma derivedResolutionFunctor_map_eq_of_homotopy {K L : CochainComplex C ℕ}
    {f g : K ⟶ L} (h : Homotopy f g) :
    (derivedResolutionFunctor F).map f = (derivedResolutionFunctor F).map g :=
  DerivedCategory.Q_map_eq_of_homotopy D
    (F.mapHomotopy (h.extend ComplexShape.embeddingUpNat))

/-- Cohomology of the localized extended image is cohomology of the original
natural-indexed image. -/
def derivedResolutionHomologyIso (K : CochainComplex C ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).obj
        ((derivedResolutionFunctor F).obj K) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n :=
  (DerivedCategory.homologyFunctorFactors D (n : ℤ)).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)) ≪≫
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).mapIso
      (DerivedPlus.mapExtendIso F K ComplexShape.embeddingUpNat).symm ≪≫
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl

omit [HasDerivedCategory C] [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
/-- The source cohomology identification is natural in the complex. -/
@[reassoc]
lemma derivedResolutionHomologyIso_hom_naturality
    {K L : CochainComplex C ℕ} (g : K ⟶ L) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map
        ((derivedResolutionFunctor F).map g) ≫
        (derivedResolutionHomologyIso F L n).hom =
      (derivedResolutionHomologyIso F K n).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) n := by
  have h₁ := (DerivedCategory.homologyFunctorFactors D (n : ℤ)).hom.naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat))
  have h₂ := extendMapIso_hom_naturality ComplexShape.embeddingUpNat F g
  have h₃ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  have h₄ : HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap g ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso F L ComplexShape.embeddingUpNat).inv (n : ℤ) =
      HomologicalComplex.homologyMap
          (DerivedPlus.mapExtendIso F K ComplexShape.embeddingUpNat).inv (n : ℤ) ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)
            ComplexShape.embeddingUpNat) (n : ℤ) :=
    (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ)) h₂).trans
        (HomologicalComplex.homologyMap_comp _ _ _))
  simp only [Functor.comp_map] at h₁
  simp only [derivedResolutionFunctor, Functor.comp_map,
    ComplexShape.Embedding.extendFunctor_map, derivedResolutionHomologyIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  erw [reassoc_of% h₁, reassoc_of% h₄, h₃]
  simp only [Category.assoc]
  rfl

/-- The existing injective-resolution model of the derived complex, regarded
in the unbounded derived category. -/
def derivedResolutionIso {A : C} (I : InjectiveResolution A) :
    (DerivedPlus.derivedComplex F ⋙ DerivedCategory.Plus.ι).obj A ≅
      (derivedResolutionFunctor F).obj I.cocomplex :=
  DerivedCategory.Plus.ι.mapIso (DerivedPlus.derivedComplexIso F I) ≪≫
    (DerivedCategory.Plus.QCompιIso D).app
      (F.mapCochainComplexPlus.obj (DerivedPlus.resolutionPlus I))

set_option backward.isDefEq.respectTransparency false in
/-- The resolution model is natural in maps of injective resolutions. -/
@[reassoc]
lemma derivedResolutionIso_hom_naturality {A B : C} {f : A ⟶ B}
    {I : InjectiveResolution A} {J : InjectiveResolution B}
    (φ : InjectiveResolution.Hom I J f) :
    (DerivedPlus.derivedComplex F ⋙ DerivedCategory.Plus.ι).map f ≫
        (derivedResolutionIso F J).hom =
      (derivedResolutionIso F I).hom ≫ (derivedResolutionFunctor F).map φ.hom := by
  have h := (DerivedCategory.Plus.QCompιIso D).hom.naturality
    (F.mapCochainComplexPlus.map (DerivedPlus.resolutionPlusMap φ))
  simp only [Functor.comp_map] at h
  simp only [derivedResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map,
    Iso.app_hom]
  rw [← Functor.map_comp_assoc, DerivedPlus.derivedComplexIso_hom_naturality F φ,
    Functor.map_comp, Category.assoc, h]
  rw [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Cohomology of the resolution model gives exactly the published
identification with the classical right derived functor. -/
lemma derivedResolutionIso_homology {A : C} (I : InjectiveResolution A) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map (derivedResolutionIso F I).hom ≫
        (derivedResolutionHomologyIso F I.cocomplex n).hom ≫
        (I.isoRightDerivedObj F n).inv =
      (DerivedPlus.homologyIso F I n).hom := by
  simp only [derivedResolutionIso, derivedResolutionHomologyIso, DerivedPlus.homologyIso,
    DerivedPlus.homologyResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Iso.app_hom, Category.assoc]
  rfl

/-- The derived comparison induced by a map from `K` to an injective resolution
of `A`. Compatibility with an augmentation is needed for its coherence, not for
this definition. -/
def derivedComparison {A : C} {K : CochainComplex C ℕ}
    (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex) :
    (derivedResolutionFunctor F).obj K ⟶
      (DerivedPlus.derivedComplex F ⋙ DerivedCategory.Plus.ι).obj A :=
  (derivedResolutionFunctor F).map φ ≫ (derivedResolutionIso F I).inv

set_option backward.isDefEq.respectTransparency false in
/-- The actual derived comparison induces the existing degreewise comparison
under the explicit source and target cohomology identifications. -/
@[reassoc]
theorem derivedComparison_homology {A : C} {K : CochainComplex C ℕ}
    (I : InjectiveResolution A) (φ : K ⟶ I.cocomplex) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map (derivedComparison F I φ) ≫
        (DerivedPlus.homologyIso F I n).hom =
      (derivedResolutionHomologyIso F K n).hom ≫ comparison F I φ n := by
  rw [← derivedResolutionIso_homology F I n]
  simp only [derivedComparison, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (DerivedCategory.homologyFunctor D (n : ℤ))
      (derivedResolutionIso F I).inv (derivedResolutionIso F I).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    derivedResolutionHomologyIso_hom_naturality_assoc]
  rfl

variable {A : C} {K : CochainComplex C ℕ}
  (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]

/-- Derived comparisons commute with maps of right resolutions. -/
@[reassoc]
theorem derivedComparison_naturality {B : C} {L : CochainComplex C ℕ}
    (η : (CochainComplex.single₀ C).obj B ⟶ L) (f : A ⟶ B) (g : K ⟶ L)
    (hg : ε ≫ g = (CochainComplex.single₀ C).map f ≫ η)
    {I : InjectiveResolution A} {J : InjectiveResolution B}
    (φ : K ⟶ I.cocomplex) (ψ : L ⟶ J.cocomplex)
    (hφ : ε ≫ φ = I.ι) (hψ : η ≫ ψ = J.ι) :
    (derivedResolutionFunctor F).map g ≫ derivedComparison F J ψ =
      derivedComparison F I φ ≫
        (DerivedPlus.derivedComplex F ⋙ DerivedCategory.Plus.ι).map f := by
  let h := DerivedPlus.descHom f I J
  have hh : Homotopy (g ≫ ψ) (φ ≫ h.hom) := homotopyOfComp ε _ _ (by
    rw [← Category.assoc, hg, Category.assoc, hψ, ← Category.assoc, hφ]
    exact h.ι_comp_hom.symm)
  have key : (derivedResolutionFunctor F).map g ≫ (derivedResolutionFunctor F).map ψ =
      (derivedResolutionFunctor F).map φ ≫ (derivedResolutionFunctor F).map h.hom := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact derivedResolutionFunctor_map_eq_of_homotopy F hh
  have hi := derivedResolutionIso_hom_naturality F h
  have hi' : (derivedResolutionFunctor F).map h.hom ≫ (derivedResolutionIso F J).inv =
      (derivedResolutionIso F I).inv ≫
        (DerivedPlus.derivedComplex F ⋙ DerivedCategory.Plus.ι).map f := by
    rw [← cancel_mono (derivedResolutionIso F J).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hi, Iso.inv_hom_id_assoc]
  unfold derivedComparison
  rw [← Category.assoc, key, Category.assoc, hi', Category.assoc]

/-- The derived comparison does not depend on the compatible lift or injective
resolution. -/
theorem derivedComparison_eq {I J : InjectiveResolution A}
    (φ : K ⟶ I.cocomplex) (ψ : K ⟶ J.cocomplex)
    (hφ : ε ≫ φ = I.ι) (hψ : ε ≫ ψ = J.ι) :
    derivedComparison F I φ = derivedComparison F J ψ := by
  have h := derivedComparison_naturality F ε ε (𝟙 A) (𝟙 K) (by simp) φ ψ hφ hψ
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- The canonical derived comparison of a right resolution, computed with
Mathlib's chosen injective resolution and the lift over the identity. -/
def derivedResolutionComparison :
    (derivedResolutionFunctor F).obj K ⟶
      (DerivedPlus.derivedComplex F ⋙ DerivedCategory.Plus.ι).obj A :=
  derivedComparison F (injectiveResolution A) (lift ε (𝟙 A) (injectiveResolution A).ι)

/-- Cohomology of the canonical derived comparison is the canonical published
degreewise comparison. -/
@[reassoc]
theorem derivedResolutionComparison_homology (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).map
        (derivedResolutionComparison F ε) ≫
        (DerivedPlus.homologyIso F (injectiveResolution A) n).hom =
      (derivedResolutionHomologyIso F K n).hom ≫ resolutionComparison F ε n :=
  derivedComparison_homology F _ _ n

/-- The canonical comparison can be computed with every compatible lift to
every injective resolution. -/
theorem derivedResolutionComparison_eq (I : InjectiveResolution A)
    (φ : K ⟶ I.cocomplex) (hφ : ε ≫ φ = I.ι) :
    derivedResolutionComparison F ε = derivedComparison F I φ :=
  derivedComparison_eq F ε _ φ (comp_lift_id ε _) hφ

/-- The canonical derived comparison is natural for maps of right resolutions. -/
@[reassoc]
theorem derivedResolutionComparison_naturality {B : C} {L : CochainComplex C ℕ}
    (η : (CochainComplex.single₀ C).obj B ⟶ L) [QuasiIso η]
    (f : A ⟶ B) (g : K ⟶ L)
    (hg : ε ≫ g = (CochainComplex.single₀ C).map f ≫ η) :
    (derivedResolutionFunctor F).map g ≫ derivedResolutionComparison F η =
      derivedResolutionComparison F ε ≫
        (DerivedPlus.derivedComplex F ⋙ DerivedCategory.Plus.ι).map f :=
  derivedComparison_naturality F ε η f g hg _ _ (comp_lift_id ε _) (comp_lift_id η _)

end Langlands.Cohomology.AcyclicResolution
