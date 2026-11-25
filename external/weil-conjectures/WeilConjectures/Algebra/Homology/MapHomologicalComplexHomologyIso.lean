/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Coherence of `Functor.mapHomologicalComplexHomologyIso`

For a functor `F : C ⥤ D` preserving homology, `F.mapHomologicalComplexHomologyIso c i` is
the canonical isomorphism expressing that `F` commutes with the homology functors of
homological complexes. We show that this isomorphism is

- natural in the functor `F` (`Functor.mapHomologicalComplexHomologyIso_hom_app_naturality`, in
  `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso`, and its
  inverse form `Functor.mapHomologicalComplexHomologyIso_inv_app_comp_map`);
- compatible with the composition of functors
  (`Functor.mapHomologicalComplexHomologyIso_comp_hom_app` and
  `Functor.map_mapHomologicalComplexCompIso_hom_app_comp_mapHomologicalComplexHomologyIso`).

-/

@[expose] public section

namespace CategoryTheory.Functor

open Category Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {ι : Type*} (c : ComplexShape ι) (i : ι)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `F.mapHomologicalComplexHomologyIso c i` is natural in the functor `F`. -/
@[reassoc]
lemma mapHomologicalComplexHomologyIso_inv_app_comp_map [Preadditive C]
    [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D] {F G : C ⥤ D}
    [F.Additive] [G.Additive] [F.PreservesHomology]
    [G.PreservesHomology] (τ : F ⟶ G) (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexHomologyIso c i).inv.app K ≫
        (HomologicalComplex.homologyFunctor D c i).map
          ((NatTrans.mapHomologicalComplex τ c).app K) =
      τ.app (K.homology i) ≫ (G.mapHomologicalComplexHomologyIso c i).inv.app K := by
  rw [← cancel_epi ((F.mapHomologicalComplexHomologyIso c i).hom.app K), Iso.hom_inv_id_app_assoc,
    ← assoc]
  exact (Iso.eq_comp_inv ((G.mapHomologicalComplexHomologyIso c i).app K)).2
    (mapHomologicalComplexHomologyIso_hom_app_naturality c i τ K)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `(F ⋙ G).mapHomologicalComplexHomologyIso c i` is the composition of
`G.mapHomologicalComplexHomologyIso c i` and of the image by `G` of
`F.mapHomologicalComplexHomologyIso c i`. -/
lemma mapHomologicalComplexHomologyIso_comp_hom_app [Preadditive C]
    [Preadditive D] [Preadditive E] [CategoryWithHomology C]
    [CategoryWithHomology D] [CategoryWithHomology E] (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesHomology]
    [G.PreservesHomology] [(F ⋙ G).PreservesHomology] (K : HomologicalComplex C c) :
    ((F ⋙ G).mapHomologicalComplexHomologyIso c i).hom.app K =
      (G.mapHomologicalComplexHomologyIso c i).hom.app ((F.mapHomologicalComplex c).obj K) ≫
        G.map ((F.mapHomologicalComplexHomologyIso c i).hom.app K) := by
  rw [mapHomologicalComplexHomologyIso_hom_app_eq, mapHomologicalComplexHomologyIso_hom_app_eq,
    mapHomologicalComplexHomologyIso_hom_app_eq]
  exact (K.sc i).mapHomologyIso_comp_hom F G

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `(F ⋙ G).mapHomologicalComplexHomologyIso c i` is the composition of the
image by `G` of the inverse of `F.mapHomologicalComplexHomologyIso c i` and of the inverse of
`G.mapHomologicalComplexHomologyIso c i`. -/
lemma mapHomologicalComplexHomologyIso_comp_inv_app [Preadditive C]
    [Preadditive D] [Preadditive E] [CategoryWithHomology C]
    [CategoryWithHomology D] [CategoryWithHomology E] (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesHomology]
    [G.PreservesHomology] [(F ⋙ G).PreservesHomology] (K : HomologicalComplex C c) :
    ((F ⋙ G).mapHomologicalComplexHomologyIso c i).inv.app K =
      G.map ((F.mapHomologicalComplexHomologyIso c i).inv.app K) ≫
        (G.mapHomologicalComplexHomologyIso c i).inv.app ((F.mapHomologicalComplex c).obj K) := by
  rw [← cancel_epi (((F ⋙ G).mapHomologicalComplexHomologyIso c i).hom.app K),
    Iso.hom_inv_id_app, mapHomologicalComplexHomologyIso_comp_hom_app, assoc,
    ← G.map_comp_assoc, Iso.hom_inv_id_app]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of `Functor.mapHomologicalComplexHomologyIso` with an isomorphism
`e : F ⋙ G ≅ H` and the induced isomorphism `Functor.mapHomologicalComplexCompIso e c`. -/
@[reassoc]
lemma map_mapHomologicalComplexCompIso_hom_app_comp_mapHomologicalComplexHomologyIso
    [Preadditive C] [Preadditive D] [Preadditive E] [CategoryWithHomology C]
    [CategoryWithHomology D] [CategoryWithHomology E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesHomology] [G.PreservesHomology]
    [H.PreservesHomology] [(F ⋙ G).PreservesHomology] (e : F ⋙ G ≅ H)
    (K : HomologicalComplex C c) :
    (HomologicalComplex.homologyFunctor E c i).map
        ((mapHomologicalComplexCompIso e c).hom.app K) ≫
        (H.mapHomologicalComplexHomologyIso c i).hom.app K =
      (G.mapHomologicalComplexHomologyIso c i).hom.app ((F.mapHomologicalComplex c).obj K) ≫
        G.map ((F.mapHomologicalComplexHomologyIso c i).hom.app K) ≫
        e.hom.app (K.homology i) := by
  rw [← assoc, ← mapHomologicalComplexHomologyIso_comp_hom_app,
]
  exact mapHomologicalComplexHomologyIso_hom_app_naturality c i e.hom K

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the inverse of `Functor.mapHomologicalComplexHomologyIso` with an
isomorphism `e : F ⋙ G ≅ H` and the induced isomorphism
`Functor.mapHomologicalComplexCompIso e c`. -/
@[reassoc]
lemma mapHomologicalComplexHomologyIso_inv_app_comp_map_compIso_inv_app
    [Preadditive C] [Preadditive D] [Preadditive E] [CategoryWithHomology C]
    [CategoryWithHomology D] [CategoryWithHomology E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesHomology] [G.PreservesHomology]
    [H.PreservesHomology] [(F ⋙ G).PreservesHomology] (e : F ⋙ G ≅ H)
    (K : HomologicalComplex C c) :
    (H.mapHomologicalComplexHomologyIso c i).inv.app K ≫
        (HomologicalComplex.homologyFunctor E c i).map
          ((mapHomologicalComplexCompIso e c).inv.app K) =
      e.inv.app (K.homology i) ≫ G.map ((F.mapHomologicalComplexHomologyIso c i).inv.app K) ≫
        (G.mapHomologicalComplexHomologyIso c i).inv.app ((F.mapHomologicalComplex c).obj K) := by
  have h := congrArg Iso.inv (Iso.ext
    (map_mapHomologicalComplexCompIso_hom_app_comp_mapHomologicalComplexHomologyIso c i e K) :
    (HomologicalComplex.homologyFunctor E c i).mapIso ((mapHomologicalComplexCompIso e c).app K) ≪≫
      (H.mapHomologicalComplexHomologyIso c i).app K =
    (G.mapHomologicalComplexHomologyIso c i).app ((F.mapHomologicalComplex c).obj K) ≪≫
      G.mapIso ((F.mapHomologicalComplexHomologyIso c i).app K) ≪≫ e.app (K.homology i))
  simpa using h

end CategoryTheory.Functor
