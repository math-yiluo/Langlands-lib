/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# The structure isomorphisms of a right derived transport of algebras

Let `F : C ⥤ C` and `G : D ⥤ D` be exact autoequivalences of abelian categories, `L : C ⥤ D` an
additive functor with `ε : L ⋙ G ≅ F ⋙ L`, and `W = IsoAlgebra.mapOfNatIso ε` the transport of
algebras with invertible structure morphism. Let `Γ_C : C ⥤ V` be additive, `Γ_D : D ⥤ V` exact,
with `γ_L : L ⋙ Γ_D ≅ Γ_C`, `γ_G : G ⋙ Γ_D ≅ Γ_D` and `γ_F : F ⋙ Γ_C ≅ Γ_C`.

On an algebra `(M, φ)` of `G`, `γ_G` and `φ` give an automorphism `Γ_D M ≅ Γ_D (G M) ≅ Γ_D M`
(`IsoAlgebra.forgetCompIsoOfIso`): for Weil sheaves on `Spec k̄` this is the Frobenius of global
sections. This file shows that, if `γ_L` intertwines these automorphisms for `γ_G` and `γ_F`, then
on derived categories the automorphism induced by `γ_G` on `Γ_D(RW N)` corresponds, under the
identification `Γ_D(RW N) ≅ RΓ_C(N)`
(`IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetCompIso`), to the automorphism of `RΓ_C(N)`
induced by `γ_F` and the derived structure isomorphism of `N`
(`IsoAlgebra.mapDerivedCategoryNatIso_forgetCompIsoOfIso_hom_app_rightDerivedFunctor_obj`).
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section ForgetCompIsoOfIso

variable {C : Type*} [Category C] {F : C ⥤ C} {V : Type*} [Category V] {Γ : C ⥤ V}

/-- The automorphism `Γ M ≅ Γ (F M) ≅ Γ M` of `Γ` on an algebra `(M, φ)`, induced by an
isomorphism `γ : F ⋙ Γ ≅ Γ` and the structure isomorphism `φ`. -/
noncomputable def forgetCompIsoOfIso (γ : F ⋙ Γ ≅ Γ) : forget F ⋙ Γ ≅ forget F ⋙ Γ :=
  Functor.isoWhiskerLeft (forget F) γ.symm ≪≫ Functor.isoWhiskerRight (strNatIso F) Γ

lemma forgetCompIsoOfIso_hom_app (γ : F ⋙ Γ ≅ Γ) (K : IsoAlgebra F) :
    (forgetCompIsoOfIso γ).hom.app K = γ.inv.app K.carrier ≫ Γ.map K.str.hom :=
  rfl

end ForgetCompIsoOfIso

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

@[reassoc]
lemma rightDerivedFunctorCompMapDerivedCategoryUnit_app
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (rightDerivedFunctorCompMapDerivedCategoryUnit F G).app X =
      DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv.app X) ≫
        G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app X) := by
  simp [rightDerivedFunctorCompMapDerivedCategoryUnit]

end CategoryTheory.Functor

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open CategoryTheory.Functor

variable {C D V : Type*} [Category C] [Category D] [Category V] [Abelian C] [Abelian D]
  [Abelian V] [HasDerivedCategory V]
  {F : C ⥤ C} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : D ⥤ D} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [HasDerivedCategory (IsoAlgebra F)] [HasDerivedCategory (IsoAlgebra G)]
  [HasDerivedCategory C]
  [HasKInjectiveResolutions (IsoAlgebra F)] [HasKInjectiveResolutions C]
  [(forget F).PreservesKInjectiveComplexes]
  {L : C ⥤ D} [L.Additive] (ε : L ⋙ G ≅ F ⋙ L)
  {ΓC : C ⥤ V} {ΓD : D ⥤ V} [ΓC.Additive] [ΓD.Additive] [PreservesFiniteLimits ΓD]
  [PreservesFiniteColimits ΓD]

/-- The identification `Γ_D ∘ RW ≅ RΓ_C ∘ For` of right derived functors on the derived category
of algebras, induced by `γ_L : L ⋙ Γ_D ≅ Γ_C`: both sides are right derived functors of
`For ⋙ Γ_C`. -/
noncomputable def rightDerivedFunctorMapOfNatIsoCompForgetCompIso (γL : L ⋙ ΓD ≅ ΓC) :
    (mapOfNatIso ε).rightDerivedFunctor ⋙ (forget G ⋙ ΓD).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ ΓC.rightDerivedFunctor :=
  rightDerivedNatIso _ _ (rightDerivedFunctorCompMapDerivedCategoryUnit _ _)
    (mapDerivedCategoryCompRightDerivedFunctorUnit _ _)
    (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ))
    (isoWhiskerRight
      { hom := NatTrans.mapHomotopyCategory (isoWhiskerLeft (forget F) γL).hom _
        inv := NatTrans.mapHomotopyCategory (isoWhiskerLeft (forget F) γL).inv _
        hom_inv_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
            NatTrans.mapHomotopyCategory_id]
        inv_hom_id := by
          rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
            NatTrans.mapHomotopyCategory_id] } DerivedCategory.Qh)

@[reassoc]
lemma rightDerivedFunctorMapOfNatIsoCompForgetCompIso_hom_fac (γL : L ⋙ ΓD ≅ ΓC)
    (X : HomotopyCategory (IsoAlgebra F) (ComplexShape.up ℤ)) :
    (rightDerivedFunctorCompMapDerivedCategoryUnit _ _).app X ≫
        (rightDerivedFunctorMapOfNatIsoCompForgetCompIso ε γL).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (isoWhiskerLeft (forget F) γL).hom (ComplexShape.up ℤ)).app X) ≫
        (mapDerivedCategoryCompRightDerivedFunctorUnit (forget F) ΓC).app X := by
  exact rightDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ)) _ X

variable [F.PreservesKInjectiveComplexes]

/-- **The derived Frobenius of a right derived transport.** If `γ_L : L ⋙ Γ_D ≅ Γ_C` intertwines
the automorphisms `Γ_D M ≅ Γ_D (G M)` and `Γ_C N ≅ Γ_C (F N)` given by `γ_G` and `γ_F`, then the
automorphism of `Γ_D(RW N)` induced by `γ_G` and the structure isomorphisms corresponds under
`Γ_D ∘ RW ≅ RΓ_C ∘ For` to the composite of `RΓ_C(N) ≅ RΓ_C(F N)` induced by `γ_F` with the derived
structure isomorphism `F N ≅ N`. -/
lemma mapDerivedCategoryNatIso_forgetCompIsoOfIso_hom_app_rightDerivedFunctor_obj
    (γL : L ⋙ ΓD ≅ ΓC) (γG : G ⋙ ΓD ≅ ΓD) (γF : F ⋙ ΓC ≅ ΓC)
    (h : ∀ X, γG.inv.app (L.obj X) ≫ ΓD.map (ε.hom.app X) ≫ γL.hom.app (F.obj X) =
      γL.hom.app X ≫ γF.inv.app X)
    (N : DerivedCategory (IsoAlgebra F)) :
    (mapDerivedCategoryNatIso (forgetCompIsoOfIso γG)).hom.app
        ((mapOfNatIso ε).rightDerivedFunctor.obj N) ≫
        (rightDerivedFunctorMapOfNatIsoCompForgetCompIso ε γL).hom.app N =
      (rightDerivedFunctorMapOfNatIsoCompForgetCompIso ε γL).hom.app N ≫
        (rightDerivedFunctorIsoMapDerivedCategoryComp γF).hom.app
          ((forget F).mapDerivedCategory.obj N) ≫
        ΓC.rightDerivedFunctor.map ((mapDerivedCategoryCompIso (forget F) F).hom.app N ≫
          (mapDerivedCategoryNatIso (strNatIso F)).hom.app N) := by
  suffices H : whiskerLeft (mapOfNatIso ε).rightDerivedFunctor
        (mapDerivedCategoryNatIso (forgetCompIsoOfIso γG)).hom ≫
        (rightDerivedFunctorMapOfNatIsoCompForgetCompIso ε γL).hom =
      (rightDerivedFunctorMapOfNatIsoCompForgetCompIso ε γL).hom ≫
        whiskerLeft (forget F).mapDerivedCategory
          (rightDerivedFunctorIsoMapDerivedCategoryComp γF).hom ≫
        whiskerRight ((mapDerivedCategoryCompIso (forget F) F).hom ≫
          (mapDerivedCategoryNatIso (strNatIso F)).hom) ΓC.rightDerivedFunctor from congr_app H N
  refine rightDerived_ext _ (rightDerivedFunctorCompMapDerivedCategoryUnit _ _)
    (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ)) _ _ _ ?_
  ext X
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [rightDerivedFunctorMapOfNatIsoCompForgetCompIso_hom_fac_assoc,
    rightDerivedFunctorCompMapDerivedCategoryUnit_app]
  simp only [Category.assoc]
  erw [(mapDerivedCategoryNatIso (forgetCompIsoOfIso γG)).hom.naturality_assoc]
  rw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app_assoc]
  have hφ : DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso
        (Iso.refl (mapOfNatIso ε ⋙ forget G ⋙ ΓD)) (ComplexShape.up ℤ)).inv.app X) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (forgetCompIsoOfIso γG).hom
        (ComplexShape.up ℤ)).app
          (((mapOfNatIso ε).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (whiskerLeft (mapOfNatIso ε) (forgetCompIsoOfIso γG).hom) (ComplexShape.up ℤ)).app X) ≫
      DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso
        (Iso.refl (mapOfNatIso ε ⋙ forget G ⋙ ΓD)) (ComplexShape.up ℤ)).inv.app X) := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have c : (mapHomotopyCategoryCompIso (Iso.refl (mapOfNatIso ε ⋙ forget G ⋙ ΓD))
        (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
    rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp]
    congr 1
    erw [c, Category.id_comp, Category.comp_id]
    rfl
  rw [reassoc_of% hφ, ← rightDerivedFunctorCompMapDerivedCategoryUnit_app_assoc,
    rightDerivedFunctorMapOfNatIsoCompForgetCompIso_hom_fac]
  rw [mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  simp only [Category.assoc]
  erw [(rightDerivedFunctorIsoMapDerivedCategoryComp γF).hom.naturality_assoc]
  rw [rightDerivedFunctorIsoMapDerivedCategoryComp_hom_fac_assoc,
    mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  simp only [Category.assoc, Functor.comp_map, ← Functor.map_comp]
  rw [mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryCompIso_inv_app_assoc,
    mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app]
  simp only [Functor.map_comp]
  erw [← ΓC.rightDerivedFunctorUnit.naturality_assoc,
    ← ΓC.rightDerivedFunctorUnit.naturality_assoc]
  simp only [Functor.comp_map, ← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have c₁ : (mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ ΓC)) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  have c₂ : (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ ΓC)) (ComplexShape.up ℤ)).inv.app
      (((forget F).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K)) = 𝟙 _ := rfl
  have c₃ : (mapHomotopyCategoryCompIso (Iso.refl (forget F ⋙ F)) (ComplexShape.up ℤ)).hom.app
      ((HomotopyCategory.quotient (IsoAlgebra F) (ComplexShape.up ℤ)).obj K) = 𝟙 _ := rfl
  erw [c₁, c₂, c₃, Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id,
    Category.id_comp, NatTrans.mapHomotopyCategory_app, NatTrans.mapHomotopyCategory_app,
    NatTrans.mapHomotopyCategory_app, NatTrans.mapHomotopyCategory_app,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  change (γG.inv.app (L.obj (K.X n).carrier) ≫
      ΓD.map (ε.hom.app (K.X n).carrier ≫ L.map (K.X n).str.hom)) ≫ γL.hom.app (K.X n).carrier =
    γL.hom.app (K.X n).carrier ≫ γF.inv.app (K.X n).carrier ≫ ΓC.map (K.X n).str.hom
  have := γL.hom.naturality (K.X n).str.hom
  simp only [Functor.comp_map] at this
  simp only [Functor.map_comp, Category.assoc, this]
  rw [reassoc_of% (h (K.X n).carrier)]

end CategoryTheory.Endofunctor.IsoAlgebra
