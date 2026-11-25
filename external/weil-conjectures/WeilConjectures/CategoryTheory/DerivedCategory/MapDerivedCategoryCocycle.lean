/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Cocycle conditions for the functors induced on derived categories

For exact functors `F : C ⥤ D`, `G : D ⥤ E`, `H : C ⥤ E` between abelian categories and an
isomorphism `γ : F ⋙ G ≅ H`, the induced functors on derived categories satisfy
`D(F) ⋙ D(G) ≅ D(H)` (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso γ`, through
`D(F ⋙ G) ≅ D(F) ⋙ D(G)`). On the image `Q K` of a complex it is the image of the levelwise
components of `γ` (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso_hom_app_Q`).

Consequently, a family of such isomorphisms satisfying the cocycle condition of an associator
(that of a pseudofunctor) on the abelian categories induces one satisfying the cocycle condition
on the derived categories (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso_cocycle`). This is
used to pass the associativity constraints of extensions of scalars to derived categories.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

section

variable {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The isomorphism `D(F) ⋙ D(G) ≅ D(H)` induced by an isomorphism `γ : F ⋙ G ≅ H` of exact
functors, through `D(F ⋙ G) ≅ D(F) ⋙ D(G)`. -/
noncomputable def mapDerivedCategoryCompNatIso (γ : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryNatIso γ

/-- The morphism of complexes `G (F K) ⟶ H K` given in each degree by the component of
`γ : F ⋙ G ≅ H`. -/
noncomputable abbrev mapHomologicalComplexCompIsoHomOfIso (γ : F ⋙ G ≅ H)
    (K : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K ≫
    (NatTrans.mapHomologicalComplex γ.hom (ComplexShape.up ℤ)).app K

/-- On the image of a complex `K`, the isomorphism `D(F) ⋙ D(G) ≅ D(H)` is, up to the
factorizations through the localization functors, the image of the levelwise components
of `γ`. -/
lemma mapDerivedCategoryCompNatIso_hom_app_Q (γ : F ⋙ G ≅ H) (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompNatIso γ).hom.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategoryFactors.hom.app K =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj K) ≫
        DerivedCategory.Q.map (mapHomologicalComplexCompIsoHomOfIso γ K) := by
  have h := mapDerivedCategoryCompIso_fac F G K
  have h' := mapDerivedCategoryNatIso_fac γ K
  simp only [mapDerivedCategoryCompNatIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, h', Functor.map_comp]
  rw [← h]
  simp

end

variable {A₁ A₂ A₃ A₄ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category A₄]
  [Abelian A₁] [Abelian A₂] [Abelian A₃] [Abelian A₄]
  [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory A₃] [HasDerivedCategory A₄]
  {F₁₂ : A₁ ⥤ A₂} {F₂₃ : A₂ ⥤ A₃} {F₃₄ : A₃ ⥤ A₄} {F₁₃ : A₁ ⥤ A₃} {F₂₄ : A₂ ⥤ A₄}
  {F₁₄ : A₁ ⥤ A₄} [F₁₂.Additive] [F₂₃.Additive] [F₃₄.Additive] [F₁₃.Additive] [F₂₄.Additive]
  [F₁₄.Additive] [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₂₃] [PreservesFiniteColimits F₂₃]
  [PreservesFiniteLimits F₃₄] [PreservesFiniteColimits F₃₄]
  [PreservesFiniteLimits F₁₃] [PreservesFiniteColimits F₁₃]
  [PreservesFiniteLimits F₂₄] [PreservesFiniteColimits F₂₄]
  [PreservesFiniteLimits F₁₄] [PreservesFiniteColimits F₁₄]

/-- **The cocycle condition passes to derived categories.** If isomorphisms
`γ_{ijk} : F_{ij} ⋙ F_{jk} ≅ F_{ik}` of exact functors satisfy the cocycle condition of an
associator, then so do the induced isomorphisms `D(F_{ij}) ⋙ D(F_{jk}) ≅ D(F_{ik})`. -/
lemma mapDerivedCategoryCompNatIso_cocycle (γ₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃)
    (γ₁₃₄ : F₁₃ ⋙ F₃₄ ≅ F₁₄) (γ₂₃₄ : F₂₃ ⋙ F₃₄ ≅ F₂₄) (γ₁₂₄ : F₁₂ ⋙ F₂₄ ≅ F₁₄)
    (h : ∀ X, F₃₄.map (γ₁₂₃.hom.app X) ≫ γ₁₃₄.hom.app X =
      γ₂₃₄.hom.app (F₁₂.obj X) ≫ γ₁₂₄.hom.app X) (K : DerivedCategory A₁) :
    F₃₄.mapDerivedCategory.map ((mapDerivedCategoryCompNatIso γ₁₂₃).hom.app K) ≫
        (mapDerivedCategoryCompNatIso γ₁₃₄).hom.app K =
      (mapDerivedCategoryCompNatIso γ₂₃₄).hom.app (F₁₂.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryCompNatIso γ₁₂₄).hom.app K := by
  suffices e : Functor.whiskerRight (mapDerivedCategoryCompNatIso γ₁₂₃).hom
      F₃₄.mapDerivedCategory ≫ (mapDerivedCategoryCompNatIso γ₁₃₄).hom =
      Functor.whiskerLeft F₁₂.mapDerivedCategory (mapDerivedCategoryCompNatIso γ₂₃₄).hom ≫
        (mapDerivedCategoryCompNatIso γ₁₂₄).hom from congr_app e K
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A₁ (ComplexShape.up ℤ)) (fun L ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (F₁₄.mapDerivedCategoryFactors.hom.app L), Category.assoc,
    mapDerivedCategoryCompNatIso_hom_app_Q, ← Functor.map_comp_assoc,
    mapDerivedCategoryCompNatIso_hom_app_Q, Category.assoc, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  have n₁ := F₃₄.mapDerivedCategoryFactors.hom.naturality
    (mapHomologicalComplexCompIsoHomOfIso γ₁₂₃ L)
  simp only [Functor.comp_map] at n₁
  rw [reassoc_of% n₁, mapDerivedCategoryCompNatIso_hom_app_Q]
  have n₂ := (mapDerivedCategoryCompNatIso γ₂₃₄).hom.naturality
    (F₁₂.mapDerivedCategoryFactors.hom.app L)
  simp only [Functor.comp_map] at n₂
  erw [← reassoc_of% n₂]
  have n₃ := mapDerivedCategoryCompNatIso_hom_app_Q γ₂₃₄ ((F₁₂.mapHomologicalComplex _).obj L)
  erw [reassoc_of% n₃]
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
  congr 4
  ext n
  simp only [mapHomologicalComplexCompIsoHomOfIso, Functor.mapHomologicalComplexCompIso_hom_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Iso.refl_hom, NatTrans.id_app, Functor.map_comp]
  erw [F₃₄.map_id, Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  exact h (L.X n)

end CategoryTheory.Functor
