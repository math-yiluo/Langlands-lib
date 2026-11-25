/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Free comparisons of exact functors on derived categories

Let `free₁ ⊣ forget₁` and `free₂ ⊣ forget₂` be adjunctions of exact functors between abelian
categories, `L` and `L'` exact functors and `c : L ⋙ forget₂ ≅ forget₁ ⋙ L'`. On derived
categories, `c` induces `D(c) : D(L) ⋙ D(forget₂) ≅ D(forget₁) ⋙ D(L')`
(`CategoryTheory.Functor.mapDerivedCategoryCompForgetIso`), and the free comparison of `D(L)` for
the derived adjunctions is an isomorphism if the free comparison of `L` is an isomorphism on all
objects (`CategoryTheory.Adjunction.isIso_freeComparison_mapDerivedCategory`).
-/

@[expose] public section

universe w₁ w₂ w₃ w₄

open CategoryTheory Limits

namespace CategoryTheory

section HomologicalComplex

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
  [Preadditive A] [Preadditive A'] [Preadditive B] [Preadditive B'] {ι : Type*}
  (cs : ComplexShape ι) {free₁ : A' ⥤ A} {forget₁ : A ⥤ A'} {free₂ : B' ⥤ B} {forget₂ : B ⥤ B'}
  [free₁.Additive] [forget₁.Additive] [free₂.Additive] [forget₂.Additive]
  {L : A ⥤ B} {L' : A' ⥤ B'} [L.Additive] [L'.Additive]

/-- The isomorphism `L ⋙ forget₂ ≅ forget₁ ⋙ L'` induced on categories of homological complexes
by `c : L ⋙ forget₂ ≅ forget₁ ⋙ L'`. -/
noncomputable def Functor.mapHomologicalComplexCompForgetIso
    (c : L ⋙ forget₂ ≅ forget₁ ⋙ L') :
    L.mapHomologicalComplex cs ⋙ forget₂.mapHomologicalComplex cs ≅
      forget₁.mapHomologicalComplex cs ⋙ L'.mapHomologicalComplex cs :=
  NatIso.mapHomologicalComplex c cs

/-- The free comparison of the induced functors on complexes is the degreewise free
comparison. -/
lemma Adjunction.freeComparison_mapHomologicalComplex_f (adj₁ : free₁ ⊣ forget₁)
    (adj₂ : free₂ ⊣ forget₂) (c : L ⋙ forget₂ ≅ forget₁ ⋙ L') (K : HomologicalComplex A' cs)
    (n : ι) :
    (freeComparison (adj₁.mapHomologicalComplex cs) (adj₂.mapHomologicalComplex cs)
      (L.mapHomologicalComplex cs) (L'.mapHomologicalComplex cs)
      (Functor.mapHomologicalComplexCompForgetIso cs c) K).f n =
      freeComparison adj₁ adj₂ L L' c (K.X n) :=
  rfl

/-- The free comparison of the induced functors on complexes is an isomorphism if the free
comparison of `L` is an isomorphism on all objects. -/
lemma Adjunction.isIso_freeComparison_mapHomologicalComplex (adj₁ : free₁ ⊣ forget₁)
    (adj₂ : free₂ ⊣ forget₂) (c : L ⋙ forget₂ ≅ forget₁ ⋙ L')
    (h : ∀ M, IsIso (freeComparison adj₁ adj₂ L L' c M)) (K : HomologicalComplex A' cs) :
    IsIso (freeComparison (adj₁.mapHomologicalComplex cs) (adj₂.mapHomologicalComplex cs)
      (L.mapHomologicalComplex cs) (L'.mapHomologicalComplex cs)
      (Functor.mapHomologicalComplexCompForgetIso cs c) K) := by
  have (n : ι) : IsIso ((freeComparison (adj₁.mapHomologicalComplex cs)
      (adj₂.mapHomologicalComplex cs) (L.mapHomologicalComplex cs) (L'.mapHomologicalComplex cs)
      (Functor.mapHomologicalComplexCompForgetIso cs c) K).f n) := by
    rw [freeComparison_mapHomologicalComplex_f]
    exact h _
  exact HomologicalComplex.Hom.isIso_of_components _

end HomologicalComplex

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Helpers

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

namespace Functor

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The inverse of `Functor.mapDerivedCategoryCompIso` on the image of a complex. -/
lemma mapDerivedCategoryCompIso_inv_app_Q (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (.up ℤ)).hom.app K) ≫
        (F ⋙ G).mapDerivedCategoryFactors.inv.app K := by
  exact mapDerivedCategoryCompIso_hom_app_Q_obj F G K

/-- `Functor.mapDerivedCategoryCompIso` on the image of a complex. -/
lemma mapDerivedCategoryCompIso_hom_app_Q (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (.up ℤ)).inv.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  rw [← cancel_mono ((mapDerivedCategoryCompIso F G).hom.app _), Iso.inv_hom_id_app,
    mapDerivedCategoryCompIso_inv_app_Q]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
  rfl

end Functor

/-- The inverse of `Functor.mapDerivedCategoryNatIso` on the image of a complex. -/
lemma Functor.mapDerivedCategoryNatIso_inv_app_Q {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : CochainComplex C ℤ) :
    (mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app K) ≫
        F.mapDerivedCategoryFactors.inv.app K := by
  rw [← cancel_epi ((mapDerivedCategoryNatIso e).hom.app _), Iso.hom_inv_id_app,
    mapDerivedCategoryNatIso_fac_assoc, ← DerivedCategory.Q.map_comp_assoc, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp, e.hom_inv_id]
  simp

end Helpers

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B'] [Abelian A]
  [Abelian A'] [Abelian B] [Abelian B'] [HasDerivedCategory.{w₁} A]
  [HasDerivedCategory.{w₂} A'] [HasDerivedCategory.{w₃} B] [HasDerivedCategory.{w₄} B']
  {free₁ : A' ⥤ A} {forget₁ : A ⥤ A'} {free₂ : B' ⥤ B} {forget₂ : B ⥤ B'}
  [free₁.Additive] [PreservesFiniteLimits free₁] [PreservesFiniteColimits free₁]
  [forget₁.Additive] [PreservesFiniteLimits forget₁] [PreservesFiniteColimits forget₁]
  [free₂.Additive] [PreservesFiniteLimits free₂] [PreservesFiniteColimits free₂]
  [forget₂.Additive] [PreservesFiniteLimits forget₂] [PreservesFiniteColimits forget₂]
  {L : A ⥤ B} {L' : A' ⥤ B'} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']

/-- The isomorphism `D(L) ⋙ D(forget₂) ≅ D(forget₁) ⋙ D(L')` induced by
`c : L ⋙ forget₂ ≅ forget₁ ⋙ L'`. -/
noncomputable def Functor.mapDerivedCategoryCompForgetIso (c : L ⋙ forget₂ ≅ forget₁ ⋙ L') :
    L.mapDerivedCategory ⋙ forget₂.mapDerivedCategory ≅
      forget₁.mapDerivedCategory ⋙ L'.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso L forget₂ ≪≫ Functor.mapDerivedCategoryNatIso c ≪≫
    (Functor.mapDerivedCategoryCompIso forget₁ L').symm

/-- The isomorphism `Functor.mapDerivedCategoryCompForgetIso c` on the image of a complex. -/
lemma Functor.mapDerivedCategoryCompForgetIso_inv_app_Q (c : L ⋙ forget₂ ≅ forget₁ ⋙ L')
    (X : CochainComplex A ℤ) :
    (mapDerivedCategoryCompForgetIso c).inv.app (DerivedCategory.Q.obj X) =
      L'.mapDerivedCategory.map (forget₁.mapDerivedCategoryFactors.hom.app X) ≫
        L'.mapDerivedCategoryFactors.hom.app ((forget₁.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map ((mapHomologicalComplexCompForgetIso (.up ℤ) c).inv.app X) ≫
        forget₂.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj X) ≫
        forget₂.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app X) := by
  rw [mapDerivedCategoryCompForgetIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, NatTrans.comp_app, mapDerivedCategoryCompIso_inv_app_Q,
    mapDerivedCategoryNatIso_inv_app_Q, mapDerivedCategoryCompIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- The free comparison of `D(L)` on the image of a complex `K`: up to the factorization
isomorphisms, it is the image of the free comparison on complexes. -/
lemma Adjunction.freeComparison_mapDerivedCategory_Q_obj (adj₁ : free₁ ⊣ forget₁)
    (adj₂ : free₂ ⊣ forget₂) (c : L ⋙ forget₂ ≅ forget₁ ⋙ L') (K : CochainComplex A' ℤ) :
    freeComparison adj₁.mapExactDerivedCategory adj₂.mapExactDerivedCategory
      L.mapDerivedCategory L'.mapDerivedCategory (Functor.mapDerivedCategoryCompForgetIso c)
      (DerivedCategory.Q.obj K) =
    free₂.mapDerivedCategory.map (L'.mapDerivedCategoryFactors.hom.app K) ≫
      free₂.mapDerivedCategoryFactors.hom.app ((L'.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map (freeComparison (adj₁.mapHomologicalComplex _)
        (adj₂.mapHomologicalComplex _) (L.mapHomologicalComplex _) (L'.mapHomologicalComplex _)
        (Functor.mapHomologicalComplexCompForgetIso _ c) K) ≫
      L.mapDerivedCategoryFactors.inv.app ((free₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
      L.mapDerivedCategory.map (free₁.mapDerivedCategoryFactors.inv.app K) := by
  have hc := (Functor.mapDerivedCategoryCompForgetIso c).inv.naturality
    (free₁.mapDerivedCategoryFactors.inv.app K)
  have hε := adj₂.mapExactDerivedCategory.counit.naturality
    (L.mapDerivedCategoryFactors.inv.app ((free₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
      L.mapDerivedCategory.map (free₁.mapDerivedCategoryFactors.inv.app K))
  dsimp at hc hε
  simp only [Functor.map_comp, Category.assoc] at hε
  have key : L'.mapDerivedCategory.map
      (DerivedCategory.Q.map ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        forget₁.mapDerivedCategoryFactors.inv.app ((free₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        forget₁.mapDerivedCategory.map (free₁.mapDerivedCategoryFactors.inv.app K)) ≫
      (Functor.mapDerivedCategoryCompForgetIso c).inv.app
        (free₁.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) =
      L'.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((L'.mapHomologicalComplex (.up ℤ)).map
          ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app K)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompForgetIso (.up ℤ) c).inv.app
          ((free₁.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        forget₂.mapDerivedCategoryFactors.inv.app
          ((L.mapHomologicalComplex (.up ℤ)).obj ((free₁.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        forget₂.mapDerivedCategory.map
          (L.mapDerivedCategoryFactors.inv.app ((free₁.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        forget₂.mapDerivedCategory.map
          (L.mapDerivedCategory.map (free₁.mapDerivedCategoryFactors.inv.app K)) := by
    simp only [Functor.map_comp, Category.assoc, hc,
      Functor.mapDerivedCategoryCompForgetIso_inv_app_Q]
    rw [← L'.mapDerivedCategory.map_comp_assoc (forget₁.mapDerivedCategoryFactors.inv.app _),
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    rfl
  rw [freeComparison, homEquiv_counit]
  simp only [localization_unit_app, Iso.symm_hom]
  rw [key]
  simp only [Functor.map_comp, Category.assoc]
  rw [hε]
  simp only [localization_counit_app, Iso.symm_inv, Category.assoc]
  rw [← free₂.mapDerivedCategory.map_comp_assoc (forget₂.mapDerivedCategoryFactors.inv.app _),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc,
    Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [freeComparison, homEquiv_counit, Functor.map_comp, Category.assoc]

/-- **Free comparisons of exact functors on derived categories.** If the free comparison
`free₂ (L' M) ⟶ L (free₁ M)` is an isomorphism for every object `M`, so is the free comparison of
`D(L)` for the derived adjunctions `D(free₁) ⊣ D(forget₁)` and `D(free₂) ⊣ D(forget₂)`. -/
theorem Adjunction.isIso_freeComparison_mapDerivedCategory (adj₁ : free₁ ⊣ forget₁)
    (adj₂ : free₂ ⊣ forget₂) (c : L ⋙ forget₂ ≅ forget₁ ⋙ L')
    (h : ∀ M, IsIso (freeComparison adj₁ adj₂ L L' c M)) (M : DerivedCategory A') :
    IsIso (freeComparison adj₁.mapExactDerivedCategory adj₂.mapExactDerivedCategory
      L.mapDerivedCategory L'.mapDerivedCategory (Functor.mapDerivedCategoryCompForgetIso c) M) :=
  have : IsIso (freeComparison adj₁.mapExactDerivedCategory adj₂.mapExactDerivedCategory
      L.mapDerivedCategory L'.mapDerivedCategory (Functor.mapDerivedCategoryCompForgetIso c)
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage M))) := by
    have := isIso_freeComparison_mapHomologicalComplex (.up ℤ) adj₁ adj₂ c h
      (DerivedCategory.Q.objPreimage M)
    rw [freeComparison_mapDerivedCategory_Q_obj]
    infer_instance
  isIso_freeComparison_of_iso _ _ _ _ _ (DerivedCategory.Q.objObjPreimageIso M).symm

end CategoryTheory
