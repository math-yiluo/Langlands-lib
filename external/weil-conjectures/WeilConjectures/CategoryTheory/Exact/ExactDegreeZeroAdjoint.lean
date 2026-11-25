/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Adjunction transposes of exact degree-zero insertions

Source: Mathlib exact-single comparisons and adjunction composition
(blueprint: def-sp-exact-degree-zero-adjoint-interface).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace SheafExactDegreeZero

/-- The adjunction transpose of an ordinary insertion under an exact right adjoint.
Source: the exact-functor single comparison and adjunction hom equivalence.
(blueprint: def-sp-exact-degree-zero-adjoint-interface) -/
@[irreducible]
def adjointInsertion
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    [HasDerivedCategory V] [HasDerivedCategory W]
    (R : W ⥤ V) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory V ⥤ DerivedCategory W} (a : L ⊣ R.mapDerivedCategory)
    {F : V} {G : W} (η : F ⟶ R.obj G) :
    L.obj ((DerivedCategory.singleFunctor V 0).obj F) ⟶
      (DerivedCategory.singleFunctor W 0).obj G :=
  (a.homEquiv _ _).symm ((DerivedCategory.singleFunctor V 0).map η ≫
    (R.mapDerivedCategorySingleFunctor 0).inv.app G)

private theorem transpose_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {U : D ⥤ C} {G : D ⥤ E} {V : E ⥤ D}
    {H : C ⥤ E} {W : E ⥤ C}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (ρ : V ⋙ U ≅ W)
    {X : C} {Y : D} {Z : E} (f : X ⟶ U.obj Y) (g : Y ⟶ V.obj Z) :
    G.map ((a.homEquiv _ _).symm f) ≫ (b.homEquiv _ _).symm g =
      (Adjunction.leftAdjointCompIso a b c ρ).hom.app X ≫
        (c.homEquiv _ _).symm (f ≫ U.map g ≫ ρ.hom.app Z) := by
  let α := Adjunction.leftAdjointCompIso a b c ρ
  have hh (k : H.obj X ⟶ Z) :
      (a.comp b).homEquiv X Z (α.hom.app X ≫ k) =
        c.homEquiv X Z k ≫ ρ.inv.app Z := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
    have hu := unit_conjugateEquiv_symm c (a.comp b) ρ.inv X
    change c.unit.app X ≫ ρ.inv.app (H.obj X) =
      (a.comp b).unit.app X ≫ (V ⋙ U).map (α.hom.app X) at hu
    rw [← hu, Category.assoc, ← ρ.inv.naturality]
    simp only [Category.assoc]
  apply ((a.comp b).homEquiv _ _).injective
  rw [hh]
  simp only [Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ _) = _
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact (congrArg (f ≫ ·) (Category.comp_id (U.map g))).symm

private theorem raw_unit_comp
    {V W X : Type*} [Category V] [Category W] [Category X]
    [Abelian V] [Abelian W] [Abelian X]
    [HasDerivedCategory V] [HasDerivedCategory W] [HasDerivedCategory X]
    (F : V ⥤ W) (G : W ⥤ X) (H : V ⥤ X)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H)
    {K : X} {L : W} {M : V}
    (f : K ⟶ G.obj L) (g : L ⟶ F.obj M) (h : K ⟶ H.obj M)
    (hh : h = f ≫ G.map g ≫ e.hom.app M) :
    (DerivedCategory.singleFunctor X 0).map h ≫
      (H.mapDerivedCategorySingleFunctor 0).inv.app M =
    ((DerivedCategory.singleFunctor X 0).map f ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app L) ≫
      G.mapDerivedCategory.map ((DerivedCategory.singleFunctor W 0).map g ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      (Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso e).hom.app
          ((DerivedCategory.singleFunctor V 0).obj M) := by
  have ht := SheafExactDegreeZero.unit_comp F G H e
    (Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e) rfl f g h hh
  unfold SheafExactDegreeZero.unit SheafExactDegreeZero.map
    SheafExactDegreeZero.comparison SheafExactDegreeZero.functor SheafExactDegreeZero.obj at ht
  exact ht

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
/-- Exact degree-zero insertion transposes compose by the canonical adjoint comparison.
Source: Mathlib's exact-functor single coherence and adjunction composition.
(blueprint: def-sp-exact-degree-zero-adjoint-interface) -/
theorem adjointInsertion_comp
    {V W X : Type*} [Category V] [Category W] [Category X]
    [Abelian V] [Abelian W] [Abelian X]
    [HasDerivedCategory V] [HasDerivedCategory W] [HasDerivedCategory X]
    (R : W ⥤ V) (S : X ⥤ W) (T : X ⥤ V)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {L : DerivedCategory V ⥤ DerivedCategory W}
    {M : DerivedCategory W ⥤ DerivedCategory X}
    {K : DerivedCategory V ⥤ DerivedCategory X}
    (a : L ⊣ R.mapDerivedCategory) (b : M ⊣ S.mapDerivedCategory)
    (c : K ⊣ T.mapDerivedCategory) (e : S ⋙ R ≅ T)
    {F : V} {G : W} {H : X}
    (η : F ⟶ R.obj G) (θ : G ⟶ S.obj H) (ζ : F ⟶ T.obj H)
    (hζ : ζ = η ≫ R.map θ ≫ e.hom.app H) :
    M.map (adjointInsertion R a η) ≫ adjointInsertion S b θ =
      (Adjunction.leftAdjointCompIso a b c
        (Functor.mapDerivedCategoryCompIso S R ≪≫
          Functor.mapDerivedCategoryNatIso e)).hom.app
            ((DerivedCategory.singleFunctor V 0).obj F) ≫ adjointInsertion T c ζ := by
  unfold adjointInsertion
  rw [raw_unit_comp S R T e η θ ζ hζ]
  exact transpose_comp a b c _ _ _

/-- A universal ordinary insertion has invertible adjunction transpose.
Source: the representing universal property and Yoneda's criterion for an isomorphism.
(blueprint: def-sp-exact-degree-zero-adjoint-interface) -/
theorem isIso_adjointInsertion
    {V W : Type*} [Category V] [Category W] [Abelian V] [Abelian W]
    [HasDerivedCategory V] [HasDerivedCategory W]
    (R : W ⥤ V) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {L : DerivedCategory V ⥤ DerivedCategory W} (a : L ⊣ R.mapDerivedCategory)
    {F : V} {G : W} (η : F ⟶ R.obj G) (hη : Universal R η) :
    IsIso (adjointInsertion R a η) := by
  apply CategoryTheory.isIso_of_coyoneda_map_bijective
  intro Z
  have hb := (universal_iff R η).mp hη Z
  have he : (fun f : (DerivedCategory.singleFunctor W 0).obj G ⟶ Z ↦
      a.homEquiv _ _ (adjointInsertion R a η ≫ f)) =
      (fun f ↦ (DerivedCategory.singleFunctor V 0).map η ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app G ≫ R.mapDerivedCategory.map f) := by
    funext f
    rw [Adjunction.homEquiv_naturality_right]
    simp only [adjointInsertion, Equiv.apply_symm_apply, Category.assoc]
  have hbij : Function.Bijective (fun f ↦ a.homEquiv _ _ (adjointInsertion R a η ≫ f)) :=
    he ▸ hb
  exact (Function.Bijective.of_comp_iff' (a.homEquiv _ _).bijective _).mp hbij

universe u
attribute [local instance 10000] scalarWeakSheafify

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory

/-- The exact adjunction insertion with all site-dependent derived data fixed once.
(blueprint: def-sp-exact-degree-zero-adjoint-interface) -/
@[irreducible]
def scalarAdjointInsertion {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    [(Sheaf.derivedRestrictScalars J φ).IsRightAdjoint]
    {F : Sheaf J (ModuleCat.{u + 1} A)} {G : Sheaf J (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) :
    (Sheaf.derivedRestrictScalars J φ).leftAdjoint.obj
        ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj G :=
  adjointInsertion (Sheaf.restrictScalars J φ)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)) η

/-- General-site scalar insertions compose via the fixed right-adjoint compositor.
(blueprint: def-sp-exact-degree-zero-adjoint-interface) -/
theorem scalarAdjointInsertion_comp {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B D : Type (u + 1)} [CommRing A] [CommRing B] [CommRing D]
    (φ : A →+* B) (ψ : B →+* D)
    [(Sheaf.derivedRestrictScalars J φ).IsRightAdjoint]
    [(Sheaf.derivedRestrictScalars J ψ).IsRightAdjoint]
    [(Sheaf.derivedRestrictScalars J (ψ.comp φ)).IsRightAdjoint]
    {F : Sheaf J (ModuleCat.{u + 1} A)}
    {G : Sheaf J (ModuleCat.{u + 1} B)}
    {H : Sheaf J (ModuleCat.{u + 1} D)}
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G)
    (θ : G ⟶ (Sheaf.restrictScalars J ψ).obj H)
    (ζ : F ⟶ (Sheaf.restrictScalars J (ψ.comp φ)).obj H)
    (hζ : ζ = η ≫ (Sheaf.restrictScalars J φ).map θ ≫
      (Sheaf.restrictScalarsCompIso J φ ψ (ψ.comp φ) rfl).hom.app H) :
    (Sheaf.derivedRestrictScalars J ψ).leftAdjoint.map
        (scalarAdjointInsertion J φ η) ≫ scalarAdjointInsertion J ψ θ =
      (Adjunction.leftAdjointCompIso
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J ψ))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J (ψ.comp φ)))
        (Sheaf.derivedRestrictScalarsCompIso J (f := φ) (g := ψ) rfl)).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj F) ≫
        scalarAdjointInsertion J (ψ.comp φ) ζ := by
  unfold scalarAdjointInsertion
  exact adjointInsertion_comp
    (Sheaf.restrictScalars J φ) (Sheaf.restrictScalars J ψ)
    (Sheaf.restrictScalars J (ψ.comp φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J (ψ.comp φ)))
    (Sheaf.restrictScalarsCompIso J φ ψ (ψ.comp φ) rfl) η θ ζ hζ

/-- A universal scalar insertion has invertible transpose on any essentially small site.
(blueprint: def-sp-exact-degree-zero-adjoint-interface) -/
theorem isIso_scalarAdjointInsertion {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    [(Sheaf.derivedRestrictScalars J φ).IsRightAdjoint]
    {F : Sheaf J (ModuleCat.{u + 1} A)} {G : Sheaf J (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G) (hη : scalarUniversal J φ F G η) :
    IsIso (scalarAdjointInsertion J φ η) := by
  unfold scalarAdjointInsertion
  apply isIso_adjointInsertion
  unfold scalarUniversal scalarUnit scalarObj Sheaf.IsDerivedBaseChange at hη
  exact hη

end SheafExactDegreeZero
