import Langlands.Cohomology.AcyclicResolution.DerivedComparison
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange

/-!
# The derived comparison for composite functors

The actual derived-category map on an acyclic object, its naturality and
independence of injective resolution, and its specified cohomology formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Langlands.Cohomology.AcyclicResolution

universe w w' w'' v v' v'' u u' u''

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w'} D] [EnoughInjectives D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasDerivedCategory.{w''} E]
  {F : C ⥤ D} [F.Additive] (G : D ⥤ E) [G.Additive]
  {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H)

/-- The specified integer-complex comparison: undo extension for `H`, apply
the inverse of the termwise composite isomorphism, and redo extension for `G`. -/
def compResolutionIso (K : CochainComplex C ℕ) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
          ComplexShape.embeddingUpNat) :=
  (DerivedPlus.mapExtendIso H K ComplexShape.embeddingUpNat).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor E).mapIso
      ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).app K).symm ≪≫
    DerivedPlus.mapExtendIso G
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ComplexShape.embeddingUpNat

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] [EnoughInjectives D]
  [HasDerivedCategory E] in
set_option backward.isDefEq.respectTransparency false in
/-- The specified integer-complex comparison is natural in the original complex. -/
@[reassoc]
lemma compResolutionIso_hom_naturality {K L : CochainComplex C ℕ} (g : K ⟶ L) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (extendMap g ComplexShape.embeddingUpNat) ≫ (compResolutionIso G e L).hom =
      (compResolutionIso G e K).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extendMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)
            ComplexShape.embeddingUpNat) := by
  have h₁ := extendMapIso_hom_naturality ComplexShape.embeddingUpNat H g
  have h₂ := congrArg (ComplexShape.embeddingUpNat.extendFunctor E).map
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.naturality g)
  have h₃ := DerivedPlus.mapExtendIso_hom_naturality G ComplexShape.embeddingUpNat
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g)
  simp only [extendMapIso, Iso.symm_hom] at h₁
  simp only [Functor.comp_map, ComplexShape.Embedding.extendFunctor_map,
    extendMap_comp] at h₂
  simp only [compResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, ComplexShape.Embedding.extendFunctor_map, Category.assoc]
  erw [reassoc_of% h₁, h₃, reassoc_of% h₂]

/-- The localized form of the specified integer-complex comparison. -/
def derivedCompResolutionIso (K : CochainComplex C ℕ) :
    (derivedResolutionFunctor H).obj K ≅
      (derivedResolutionFunctor G).obj ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  DerivedCategory.Q.mapIso (compResolutionIso G e K)

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] [EnoughInjectives D] in
set_option backward.isDefEq.respectTransparency false in
/-- The localized source comparison is natural in the complex. -/
@[reassoc]
lemma derivedCompResolutionIso_hom_naturality {K L : CochainComplex C ℕ} (g : K ⟶ L) :
    (derivedResolutionFunctor H).map g ≫ (derivedCompResolutionIso G e L).hom =
      (derivedCompResolutionIso G e K).hom ≫
        (derivedResolutionFunctor G).map
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) := by
  simpa only [derivedResolutionFunctor, derivedCompResolutionIso, Functor.comp_map,
    ComplexShape.Embedding.extendFunctor_map, Functor.mapIso_hom,
    ← Functor.map_comp] using
    congrArg DerivedCategory.Q.map (compResolutionIso_hom_naturality G e g)

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] [EnoughInjectives D] in
set_option backward.isDefEq.respectTransparency false in
/-- The cohomology of the source comparison is the inverse termwise composite
isomorphism, under the two specified extension and localization comparisons. -/
@[reassoc]
lemma derivedCompResolutionIso_homology (K : CochainComplex C ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor E (n : ℤ)).map
        (derivedCompResolutionIso G e K).hom ≫
        (derivedResolutionHomologyIso G
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n).hom =
      (derivedResolutionHomologyIso H K n).hom ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.app K) n := by
  have h₁ := (DerivedCategory.homologyFunctorFactors E (n : ℤ)).hom.naturality
    (compResolutionIso G e K).hom
  have h₂ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.app K)
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  simp only [Functor.comp_map] at h₁
  simp only [derivedCompResolutionIso, derivedResolutionHomologyIso,
    Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  erw [reassoc_of% h₁]
  simp only [compResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (HomologicalComplex.homologyFunctor E _ (n : ℤ))
      (DerivedPlus.mapExtendIso G
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        ComplexShape.embeddingUpNat).hom
      (DerivedPlus.mapExtendIso G
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        ComplexShape.embeddingUpNat).inv,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [ComplexShape.Embedding.extendFunctor_map]
  erw [h₂]

variable [PreservesFiniteLimits F]

/-- The composite comparison computed with a specified injective resolution.
The acyclicity of `A` makes `F I` a right resolution of `F A`. -/
def derivedCompComparisonWithResolution {A : C} (I : InjectiveResolution A)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).obj A ⟶
      (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).obj (F.obj A) :=
  have := quasiIso_mapAugmentation F I hA
  (derivedResolutionIso H I).hom ≫ (derivedCompResolutionIso G e I.cocomplex).hom ≫
    derivedResolutionComparison G (mapAugmentation F I)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality for a supplied morphism between the injective resolutions used
to compute the two composite comparisons. -/
@[reassoc]
lemma derivedCompComparisonWithResolution_naturality {A B : C} {f : A ⟶ B}
    {I : InjectiveResolution A} {J : InjectiveResolution B}
    (φ : InjectiveResolution.Hom I J f)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A))
    (hB : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj B)) :
    (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).map f ≫
        derivedCompComparisonWithResolution G e J hB =
      derivedCompComparisonWithResolution G e I hA ≫
        (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).map (F.map f) := by
  have := quasiIso_mapAugmentation F I hA
  have := quasiIso_mapAugmentation F J hB
  have h := derivedResolutionComparison_naturality G (mapAugmentation F I)
    (mapAugmentation F J) (F.map f)
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)
    (mapAugmentation_naturality F f I J φ.hom φ.ι_comp_hom)
  simp only [derivedCompComparisonWithResolution, Category.assoc]
  erw [derivedResolutionIso_hom_naturality_assoc H φ,
    derivedCompResolutionIso_hom_naturality_assoc G e φ.hom, h]

/-- The composite comparison is independent of the chosen injective resolution. -/
lemma derivedCompComparisonWithResolution_eq {A : C} (I J : InjectiveResolution A)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    derivedCompComparisonWithResolution G e I hA =
      derivedCompComparisonWithResolution G e J hA := by
  have h := derivedCompComparisonWithResolution_naturality G e
    (DerivedPlus.descHom (𝟙 A) I J) hA hA
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- The canonical actual derived comparison, using Mathlib's chosen injective
resolution of the acyclic object. -/
def derivedCompComparison (A : C)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).obj A ⟶
      (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).obj (F.obj A) :=
  derivedCompComparisonWithResolution G e (injectiveResolution A) hA

/-- Every injective resolution computes the canonical composite comparison. -/
lemma derivedCompComparison_eq {A : C} (I : InjectiveResolution A)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    derivedCompComparison G e A hA = derivedCompComparisonWithResolution G e I hA :=
  derivedCompComparisonWithResolution_eq G e _ _ hA

/-- The canonical composite comparison is natural on acyclic objects. -/
@[reassoc]
lemma derivedCompComparison_naturality {A B : C} (f : A ⟶ B)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A))
    (hB : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj B)) :
    (DerivedPlus.derivedComplex H ⋙ DerivedCategory.Plus.ι).map f ≫
        derivedCompComparison G e B hB =
      derivedCompComparison G e A hA ≫
        (DerivedPlus.derivedComplex G ⋙ DerivedCategory.Plus.ι).map (F.map f) :=
  derivedCompComparisonWithResolution_naturality G e
    (DerivedPlus.descHom f (injectiveResolution A) (injectiveResolution B)) hA hB

set_option backward.isDefEq.respectTransparency false in
/-- The cohomology formula with an arbitrary source resolution and the chosen
target resolution, with every transporting isomorphism specified. -/
@[reassoc]
lemma derivedCompComparisonWithResolution_homology {A : C} (I : InjectiveResolution A)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) (n : ℕ) :
    have := quasiIso_mapAugmentation F I hA
    (DerivedCategory.homologyFunctor E (n : ℤ)).map
        (derivedCompComparisonWithResolution G e I hA) ≫
        (DerivedPlus.homologyIso G (injectiveResolution (F.obj A)) n).hom =
      (DerivedPlus.homologyIso H I n).hom ≫ (I.isoRightDerivedObj H n).hom ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).inv.app I.cocomplex) n ≫
        resolutionComparison G (mapAugmentation F I) n := by
  have := quasiIso_mapAugmentation F I hA
  rw [← derivedResolutionIso_homology H I n]
  simp only [derivedCompComparisonWithResolution, Functor.map_comp, Category.assoc]
  rw [derivedResolutionComparison_homology, derivedCompResolutionIso_homology_assoc,
    Iso.inv_hom_id_assoc]

/-- Nonnegative cohomology of the actual derived comparison is exactly the
published degreewise `compComparison`, through the specified identifications. -/
@[reassoc]
lemma derivedCompComparison_homology (A : C)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) (n : ℕ) :
    (DerivedCategory.homologyFunctor E (n : ℤ)).map (derivedCompComparison G e A hA) ≫
        (DerivedPlus.homologyIso G (injectiveResolution (F.obj A)) n).hom =
      (DerivedPlus.homologyIso H (injectiveResolution A) n).hom ≫
        compComparison G e A hA n :=
  derivedCompComparisonWithResolution_homology G e (injectiveResolution A) hA n

end Langlands.Cohomology.AcyclicResolution
