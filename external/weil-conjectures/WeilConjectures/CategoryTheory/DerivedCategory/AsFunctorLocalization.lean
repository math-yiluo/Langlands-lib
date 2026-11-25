/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import Mathlib.Algebra.Homology.Functor

/-!
# Levelwise localization of complexes of diagrams

For a complex `K` of diagrams `I ⥤ C`, the diagram `K.asFunctor ⋙ DerivedCategory.Q` of
localized levels only depends on the image of `K` in the derived category of diagrams: an
isomorphism `Q K ≅ Q L` induces an isomorphism of diagrams
`K.asFunctor ⋙ Q ≅ L.asFunctor ⋙ Q`. The components are the images of the isomorphism under the
exact evaluation functors.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {I : Type*} [SmallCategory I] {C : Type*} [Category C] [Abelian C]
  [HasDerivedCategory C] [HasDerivedCategory (I ⥤ C)]

/-- The level `i` of the localized diagram of a complex of diagrams is the image of the localized
complex under derived evaluation at `i`. -/
noncomputable def asFunctorCompQObjIso (K : CochainComplex (I ⥤ C) ℤ) (i : I) :
    DerivedCategory.Q.obj (K.asFunctor.obj i) ≅
      ((evaluation I C).obj i).mapDerivedCategory.obj (DerivedCategory.Q.obj K) :=
  (((evaluation I C).obj i).mapDerivedCategoryFactors.app K).symm

/-- An isomorphism of localized complexes of diagrams induces an isomorphism of the localized
level diagrams. -/
noncomputable def asFunctorCompQIsoOfIso {K L : CochainComplex (I ⥤ C) ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    K.asFunctor ⋙ DerivedCategory.Q ≅ L.asFunctor ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun i ↦ asFunctorCompQObjIso K i ≪≫ ((evaluation I C).obj i).mapDerivedCategory.mapIso e ≪≫
      (asFunctorCompQObjIso L i).symm)
    (by
      intro i j f
      let τ : (evaluation I C).obj i ⟶ (evaluation I C).obj j := (evaluation I C).map f
      have hK := Functor.mapDerivedCategoryNatTrans_fac τ K
      have hL := Functor.mapDerivedCategoryNatTrans_fac τ L
      have hK' : DerivedCategory.Q.map (K.asFunctor.map f) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) :=
        rfl
      have hL' : DerivedCategory.Q.map (L.asFunctor.map f) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app L) :=
        rfl
      have hn := (Functor.mapDerivedCategoryNatTrans τ).naturality e.hom
      have hK'' : (Functor.mapDerivedCategoryNatTrans τ).app (DerivedCategory.Q.obj K) =
          ((evaluation I C).obj i).mapDerivedCategoryFactors.hom.app K ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
              ((evaluation I C).obj j).mapDerivedCategoryFactors.inv.app K := by
        rw [← reassoc_of% hK, Iso.hom_inv_id_app]; exact (Category.comp_id _).symm
      change DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) ≫
          ((evaluation I C).obj j).mapDerivedCategoryFactors.inv.app K ≫
          ((evaluation I C).obj j).mapDerivedCategory.map e.hom ≫
          ((evaluation I C).obj j).mapDerivedCategoryFactors.hom.app L =
        (((evaluation I C).obj i).mapDerivedCategoryFactors.inv.app K ≫
          ((evaluation I C).obj i).mapDerivedCategory.map e.hom ≫
          ((evaluation I C).obj i).mapDerivedCategoryFactors.hom.app L) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app L)
      rw [Category.assoc, Category.assoc, ← hL, reassoc_of% hn, hK'']
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc])

end HomologicalComplex
