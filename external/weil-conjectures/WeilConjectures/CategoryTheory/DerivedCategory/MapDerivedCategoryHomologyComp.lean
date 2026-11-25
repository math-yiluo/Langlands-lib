/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.MapHomologicalComplexHomologyIso
public import WeilConjectures.Algebra.Homology.ShortComplex.MapHomologyIsoComp
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# The homology isomorphism of a composite of exact functors

For exact functors `F : C ⥤ D` and `G : D ⥤ E` between abelian categories, the commutation
isomorphism `Hⁿ ⋙ (F ⋙ G) ≅ D(F ⋙ G) ⋙ Hⁿ` of `F ⋙ G` with the homology functors is the
composite of those of `F` and `G`, through the composition isomorphism
`D(F ⋙ G) ≅ D(F) ⋙ D(G)` (`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp`).
Consequently, the isomorphism `D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by an isomorphism
`e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` of exact functors is `e` on homology
(`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_squareIso`).

-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The homology isomorphism of a composite of exact functors**: the commutation of `F ⋙ G`
with the homology functors is the composite of the commutations of `F` and `G`, through the
composition isomorphism `D(F ⋙ G) ≅ D(F) ⋙ D(G)`. -/
@[reassoc]
lemma mapDerivedCategoryHomologyFunctorIso_comp (n : ℤ) (K : DerivedCategory C) :
    ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor E n).map ((mapDerivedCategoryCompIso F G).inv.app K) =
      G.map ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj K) := by
  have h : ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom ≫
      whiskerRight (mapDerivedCategoryCompIso F G).inv (DerivedCategory.homologyFunctor E n) =
      whiskerRight (F.mapDerivedCategoryHomologyFunctorIso n).hom G ≫
        whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso n).hom := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun L => ?_)
    have hfac : (F ⋙ G).mapDerivedCategoryFactors.inv.app L ≫
        (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj L) =
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L) := by
      rw [← cancel_epi ((F ⋙ G).mapDerivedCategoryFactors.hom.app L), Iso.hom_inv_id_app_assoc,
        ← mapDerivedCategoryCompIso_fac F G L, mapHomologicalComplexCompIso_refl_hom_app]
      simp
    have hG : G.map ((DerivedCategory.homologyFunctor D n).map
        (F.mapDerivedCategoryFactors.inv.app L)) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) =
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L)) ≫
        (DerivedCategory.homologyFunctor E n).map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L)) :=
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality _
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      mapDerivedCategoryHomologyFunctorIso_hom_app_Q, Category.assoc, Functor.map_comp]
    rw [← Functor.map_comp, hfac, hG, mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
      mapHomologicalComplexHomologyIso_comp_inv_app]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    simp
    rfl
  exact congr_app h K

section Square

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- **The isomorphism induced on derived categories by an isomorphism of composites of exact
functors is the original isomorphism on homology**: for `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂`, the
isomorphism `D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` is `e` on the homology objects, through the
commutations of the exact functors with homology. -/
@[reassoc]
lemma mapDerivedCategoryHomologyFunctorIso_squareIso (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (n : ℤ)
    (K : DerivedCategory A) :
    F₂.map ((F₁.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (F₂.mapDerivedCategoryHomologyFunctorIso n).hom.app (F₁.mapDerivedCategory.obj K) ≫
        (DerivedCategory.homologyFunctor E n).map ((mapDerivedCategorySquareIso e).hom.app K) =
      e.hom.app ((DerivedCategory.homologyFunctor A n).obj K) ≫
        G₂.map ((G₁.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (G₂.mapDerivedCategoryHomologyFunctorIso n).hom.app (G₁.mapDerivedCategory.obj K) := by
  rw [← mapDerivedCategoryHomologyFunctorIso_comp_assoc,
    ← mapDerivedCategoryHomologyFunctorIso_comp,
    mapDerivedCategoryHomologyFunctorIso_hom_app_naturality_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    ← Functor.map_comp_assoc]
  simp

end Square

end CategoryTheory.Functor
