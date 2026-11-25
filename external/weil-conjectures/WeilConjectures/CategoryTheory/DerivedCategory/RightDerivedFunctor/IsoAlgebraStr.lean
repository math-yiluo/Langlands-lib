/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraHomology
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-!
# The structure isomorphism of a right derived functor of algebras

Let `F`, `G` be exact additive endofunctors of abelian categories `C`, `D`, `L : C ⥤ D` an
additive functor and `e : L ⋙ G ≅ F ⋙ L`, transporting `L` to
`M = IsoAlgebra.mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G`. For an algebra `K` and an
injective resolution `I` of `K` in `IsoAlgebra F`, the `r`-th homology of `RM(K[0])` has
underlying object the `r`-th homology of the complex `L(I)`
(`CategoryTheory.Endofunctor.IsoAlgebra.homologyRightDerivedFunctorForgetIso`), and its structure
isomorphism is the map induced on homology by the structure isomorphisms
`G (L Iⁿ) ≅ L (F Iⁿ) ≅ L Iⁿ` of the terms of `M(I)`
(`CategoryTheory.Endofunctor.IsoAlgebra.str_homologyRightDerivedFunctorForgetIso`).
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {F : C ⥤ C} {G : D ⥤ D} [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory (IsoAlgebra F)] [HasDerivedCategory (IsoAlgebra G)]
  [EnoughInjectives (IsoAlgebra F)] [HasKInjectiveResolutions (IsoAlgebra F)]

/-- The complex `M(I)` of algebras, for an injective resolution `I` and `M = mapOfNatIso e`. -/
noncomputable abbrev mapResolution {K : IsoAlgebra F} (I : InjectiveResolution K) :
    CochainComplex (IsoAlgebra G) ℕ :=
  ((mapOfNatIso e).mapHomologicalComplex _).obj I.cocomplex

/-- The underlying object of the `r`-th homology of `RM(K[0])`, `M = mapOfNatIso e`, is the
`r`-th homology of `M(I)` for an injective resolution `I` of `K`. -/
noncomputable def homologyRightDerivedFunctorForgetIso {K : IsoAlgebra F}
    (I : InjectiveResolution K) (r : ℕ) :
    (forget G).obj ((DerivedCategory.homologyFunctor _ r).obj
        ((mapOfNatIso e).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj K))) ≅
      (((mapResolution e I).sc r).map (forget G)).homology :=
  (forget G).mapIso ((mapOfNatIso e).homologyRightDerivedFunctorObjSingleFunctorIso K r ≪≫
      I.isoRightDerivedObj (mapOfNatIso e) r) ≪≫
    (((mapResolution e I).sc r).mapHomologyIso (forget G)).symm

/-- **The structure isomorphism of a right derived functor of algebras.** Through
`homologyRightDerivedFunctorForgetIso`, the structure isomorphism of `Hʳ(RM(K[0]))` is the map
induced on homology by the structure isomorphisms of the terms of `M(I)`. -/
theorem str_homologyRightDerivedFunctorForgetIso {K : IsoAlgebra F}
    (I : InjectiveResolution K) (r : ℕ) :
    ((DerivedCategory.homologyFunctor _ r).obj ((mapOfNatIso e).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj K))).str.hom ≫
        (homologyRightDerivedFunctorForgetIso e I r).hom =
      G.map (homologyRightDerivedFunctorForgetIso e I r).hom ≫
        ((((mapResolution e I).sc r).map (forget G)).mapHomologyIso G).inv ≫
        ShortComplex.homologyMap (((mapResolution e I).sc r).mapNatTrans (strNatIso G).hom) := by
  have h := homologyMap_mapNatTrans_strNatIso_hom G ((mapResolution e I).sc r)
  have h' : ((((mapResolution e I).sc r).map (forget G)).mapHomologyIso G).inv ≫
      ShortComplex.homologyMap (((mapResolution e I).sc r).mapNatTrans (strNatIso G).hom) =
      G.map (((mapResolution e I).sc r).mapHomologyIso (forget G)).hom ≫
        ((mapResolution e I).sc r).homology.str.hom ≫
          (((mapResolution e I).sc r).mapHomologyIso (forget G)).inv := by
    rw [← cancel_mono (((mapResolution e I).sc r).mapHomologyIso (forget G)).hom]
    simpa using h
  have hα := ((mapOfNatIso e).homologyRightDerivedFunctorObjSingleFunctorIso K r ≪≫
    I.isoRightDerivedObj (mapOfNatIso e) r).hom.hom.h
  simp only [Iso.trans_hom, comp_hom_f, Functor.map_comp, Category.assoc] at hα
  simp only [homologyRightDerivedFunctorForgetIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc, h', forget_map, str_hom]
  rw [Iso.inv_hom_id_map_assoc]
  simp only [comp_hom_f, Functor.map_comp, Category.assoc]
  have hβ := hα =≫ (((mapResolution e I).sc r).mapHomologyIso (forget G)).inv
  simp only [Category.assoc] at hβ
  exact hβ.symm

omit [HasDerivedCategory (IsoAlgebra F)] [HasDerivedCategory (IsoAlgebra G)]
  [EnoughInjectives (IsoAlgebra F)] [HasKInjectiveResolutions (IsoAlgebra F)]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The forgetful functor from algebras of an autoequivalence preserves injective objects, being
right adjoint to the exact free algebra functor. -/
lemma preservesInjectiveObjects_forget [F.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) C]
    [HasExactColimitsOfShape (Discrete ℤ) C] : (forget F).PreservesInjectiveObjects :=
  have := Functor.preservesFiniteLimits_of_preservesHomology (Free.functor F)
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (Free.adjunction F)

section Frobenius

variable {E : Type*} [Category E] [Abelian E] (ΓD : D ⥤ E) [ΓD.Additive]
  [PreservesFiniteLimits ΓD] [PreservesFiniteColimits ΓD] (ΓC : C ⥤ E) [ΓC.Additive]
  (κ : L ⋙ ΓD ≅ ΓC) (τ : ΓD ⟶ G ⋙ ΓD)

/-- The Frobenius `Γ_C(a) ≅ Γ_D(L a) ⟶ Γ_D(G (L a)) ≅ Γ_D(L (F a)) ⟶ Γ_D(L a) ≅ Γ_C(a)` of an
algebra `a`, built from `τ : Γ_D ⟶ G ⋙ Γ_D`, `e` and the structure isomorphism of `a`. -/
@[simps]
noncomputable def frobeniusNatTrans : forget F ⋙ ΓC ⟶ forget F ⋙ ΓC where
  app X := κ.inv.app X.carrier ≫ τ.app (L.obj X.carrier) ≫
    ΓD.map (e.hom.app X.carrier ≫ L.map X.str.hom) ≫ κ.hom.app X.carrier
  naturality X Y f := by
    have h1 := κ.inv.naturality f.hom.f
    have h2 := τ.naturality (L.map f.hom.f)
    have h3 := e.hom.naturality f.hom.f
    have h4 := f.hom.h
    have h5 := κ.hom.naturality f.hom.f
    simp only [Functor.comp_obj, Functor.comp_map] at h1 h2 h3 h5
    simp only [Functor.comp_obj, Functor.comp_map, forget_map, str_hom, Category.assoc]
    rw [reassoc_of% h1, reassoc_of% h2, ← h5, ← ΓD.map_comp_assoc, ← ΓD.map_comp_assoc,
      Category.assoc, ← L.map_comp, ← h4, L.map_comp, reassoc_of% h3, ΓD.map_comp_assoc]

/-- The global sections `Γ_D` of the `r`-th homology of `RM(K[0])` are the `r`-th homology of
the complex `Γ_C(I)` of global sections of an injective resolution `I` of `K`. -/
noncomputable def globalSectionsHomologyIso {K : IsoAlgebra F} (I : InjectiveResolution K)
    (r : ℕ) :
    ΓD.obj ((forget G).obj ((DerivedCategory.homologyFunctor _ r).obj
        ((mapOfNatIso e).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj K)))) ≅
      ((I.cocomplex.sc r).map (forget F ⋙ ΓC)).homology :=
  ΓD.mapIso (homologyRightDerivedFunctorForgetIso e I r) ≪≫
    ((((mapResolution e I).sc r).map (forget G)).mapHomologyIso ΓD).symm ≪≫
      ShortComplex.homologyMapIso
        ((I.cocomplex.sc r).mapNatIso (Functor.isoWhiskerLeft (forget F) κ))

/-- **The Frobenius of a right derived functor of algebras.** The Frobenius
`Γ_D(H) ⟶ Γ_D(G H) ⟶ Γ_D(H)` of the `r`-th homology `H` of `RM(K[0])`, built from
`τ : Γ_D ⟶ G ⋙ Γ_D` and the structure isomorphism of `H`, is the map induced on the `r`-th
homology of `Γ_C(I)` by the Frobenius `frobeniusNatTrans` of the terms of `I`. -/
theorem frobenius_globalSectionsHomologyIso {K : IsoAlgebra F} (I : InjectiveResolution K)
    (r : ℕ) :
    (τ.app _ ≫ ΓD.map ((DerivedCategory.homologyFunctor _ r).obj
        ((mapOfNatIso e).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj K))).str.hom) ≫
        (globalSectionsHomologyIso e ΓD ΓC κ I r).hom =
      (globalSectionsHomologyIso e ΓD ΓC κ I r).hom ≫
        ShortComplex.homologyMap
          ((I.cocomplex.sc r).mapNatTrans (frobeniusNatTrans e ΓD ΓC κ τ)) := by
  have hstr := ΓD.congr_map (str_homologyRightDerivedFunctorForgetIso e I r)
  have key₁ := ShortComplex.homologyMap_mapNatTrans
    (((mapResolution e I).sc r).map (forget G)) τ
  rw [ShortComplex.mapHomologyIso_comp] at key₁
  have key₂ := ShortComplex.mapHomologyIso_hom_naturality
    (((mapResolution e I).sc r).mapNatTrans (strNatIso G).hom) ΓD
  have k₁ : τ.app _ ≫ ΓD.map ((((mapResolution e I).sc r).map (forget G)).mapHomologyIso G).inv =
      ((((mapResolution e I).sc r).map (forget G)).mapHomologyIso ΓD).inv ≫
        ShortComplex.homologyMap ((((mapResolution e I).sc r).map (forget G)).mapNatTrans τ) ≫
          (((((mapResolution e I).sc r).map (forget G)).map G).mapHomologyIso ΓD).hom := by
    rw [key₁]
    simp
  simp only [globalSectionsHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    ShortComplex.homologyMapIso_hom, Category.assoc]
  rw [← ΓD.map_comp_assoc, hstr, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc]
  erw [← τ.naturality_assoc]
  congr 1
  rw [reassoc_of% k₁]
  erw [← reassoc_of% key₂]
  simp only [Iso.hom_inv_id_assoc, ← ShortComplex.homologyMap_comp]
  congr 2
  ext
  all_goals
    simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      ShortComplex.mapNatIso, Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₂,
      Functor.mapShortComplex_map_τ₃, frobeniusNatTrans_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app]
    erw [Iso.hom_inv_id_app_assoc]
    rfl

end Frobenius

end CategoryTheory.Endofunctor.IsoAlgebra
