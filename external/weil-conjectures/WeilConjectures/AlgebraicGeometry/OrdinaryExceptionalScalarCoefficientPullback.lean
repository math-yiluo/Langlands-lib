/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryExceptionalScalarTensorData
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! The constant coefficient model respects canonical pullback.
Source: Zheng Construction 2.26; Stacks 07A4 and 07A6
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Functor

variable {C D₁ D₂ : Type*} [Category C] [Category D₁] [Category D₂]
  [Abelian C] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C] [HasDerivedCategory D₁] [HasDerivedCategory D₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A square of exact functors `c₁ ⋙ P ≅ c₂`, together with a square of objects relating
`P X₁ ≅ X₂` to `c₁ N` and `c₂ N`, gives the corresponding square of degree-zero objects in
the derived categories, for any derived functor `L ≅ D(P)`.
Source: Stacks Project, Tag 05QI (exact functors on derived categories)
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/
theorem mapDerivedCategorySingleFunctor_constant_pullback_square
    (c₁ : C ⥤ D₁) (c₂ : C ⥤ D₂) (P : D₁ ⥤ D₂)
    [c₁.Additive] [PreservesFiniteLimits c₁] [PreservesFiniteColimits c₁]
    [c₂.Additive] [PreservesFiniteLimits c₂] [PreservesFiniteColimits c₂]
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (L : DerivedCategory D₁ ⥤ DerivedCategory D₂) (lam : L ≅ P.mapDerivedCategory)
    (σ : c₁ ⋙ P ≅ c₂) (N : C) {X₁ : D₁} {X₂ : D₂}
    (α₁ : X₁ ≅ c₁.obj N) (α₂ : X₂ ≅ c₂.obj N) (β : P.obj X₁ ≅ X₂)
    (h : P.map α₁.hom ≫ σ.hom.app N = β.hom ≫ α₂.hom) :
    L.map ((DerivedCategory.singleFunctor D₁ 0).mapIso α₁ ≪≫
        ((c₁.mapDerivedCategorySingleFunctor 0).app N).symm).hom ≫
      ((isoWhiskerLeft c₁.mapDerivedCategory lam ≪≫
        mapDerivedCategoryCompIso c₁ P ≪≫
        mapDerivedCategoryNatIso σ).app ((DerivedCategory.singleFunctor C 0).obj N)).hom =
      (lam.app _ ≪≫ (P.mapDerivedCategorySingleFunctor 0).app X₁ ≪≫
        (DerivedCategory.singleFunctor D₂ 0).mapIso β).hom ≫
      ((DerivedCategory.singleFunctor D₂ 0).mapIso α₂ ≪≫
        ((c₂.mapDerivedCategorySingleFunctor 0).app N).symm).hom := by
  have h1 := mapDerivedCategoryCompIso_hom_app_singleFunctor c₁ P N
  have h2 := mapDerivedCategoryNatIso_hom_app_singleFunctor σ N
  have h3 := (P.mapDerivedCategorySingleFunctor 0).hom.naturality α₁.hom
  have h2' : (mapDerivedCategoryNatIso σ).hom.app ((DerivedCategory.singleFunctor C 0).obj N) =
      ((c₁ ⋙ P).mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor D₂ 0).map (σ.hom.app N) ≫
          (c₂.mapDerivedCategorySingleFunctor 0).inv.app N := by
    rw [← reassoc_of% h2, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h1' : (mapDerivedCategoryCompIso c₁ P).hom.app
        ((DerivedCategory.singleFunctor C 0).obj N) ≫
      ((c₁ ⋙ P).mapDerivedCategorySingleFunctor 0).hom.app N =
      P.mapDerivedCategory.map ((c₁.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
        (P.mapDerivedCategorySingleFunctor 0).hom.app (c₁.obj N) := by
    rw [← h1, Iso.hom_inv_id_app_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, mapIso_hom, Iso.app_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerLeft_app, Functor.map_comp, Category.assoc, Iso.app_inv]
  erw [lam.hom.naturality_assoc, lam.hom.naturality_assoc]
  congr 1
  rw [h2', reassoc_of% h1']
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, reassoc_of% h3]
  rw [← h, Functor.map_comp, Category.assoc]

end CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {D : Type*} [Category* D] [HasWeakSheafify J D]
  {B' : Type*} [Category* B'] (U : D ⥤ B') [HasWeakSheafify J B']
  [J.PreservesSheafification U] [J.HasSheafCompose U]

/-- The unit of the constant sheaf adjunction is compatible with the comparison
`constantCommuteCompose` between constant sheaves and postcomposition with `U`.
Source: Stacks Project, Tag 093W (constant sheaves)
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/
theorem map_constantSheafAdj_unit_comp_constantCommuteCompose {T : C} (hT : IsTerminal T)
    (X : D) :
    U.map ((constantSheafAdj J D hT).unit.app X) ≫
        ((constantCommuteCompose J U).hom.app X).hom.app (Opposite.op T) =
      (constantSheafAdj J B' hT).unit.app (U.obj X) := by
  apply ((constantSheafAdj J B' hT).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  erw [Adjunction.left_triangle_components]
  have h₁ := (constantSheafAdj J B' hT).counit.naturality
    ((constantCommuteCompose J U).hom.app X)
  have h₂ := (constantCommuteCompose J U).hom.naturality ((constantSheafAdj J D hT).unit.app X)
  have h₃ := constantSheafAdj_counit_w J U ((constantSheaf J D).obj X) hT
  have h₂' : (constantSheaf J B').map (U.map ((constantSheafAdj J D hT).unit.app X)) =
      (constantCommuteCompose J U).inv.app X ≫
        (sheafCompose J U).map ((constantSheaf J D).map ((constantSheafAdj J D hT).unit.app X)) ≫
          (constantCommuteCompose J U).hom.app _ := by
    erw [h₂, Iso.inv_hom_id_app_assoc]
    rfl
  rw [Functor.map_comp, Category.assoc]
  erw [h₁, reassoc_of% h₂']
  erw [reassoc_of% h₃]
  rw [← Functor.map_comp_assoc, Adjunction.left_triangle_components, Functor.map_id,
    Category.id_comp]
  exact Iso.inv_hom_id_app _ _


open MonoidalCategory Functor.LaxMonoidal in
/-- The unit of the lax monoidal functor `sheafToPresheaf`, evaluated at a terminal object,
is the unit of the constant sheaf adjunction at the monoidal unit.
Source: Stacks Project, Tag 093W (constant sheaves)
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/
theorem Sheaf.ε_sheafToPresheaf_app_eq_constantSheafAdj_unit {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A' : Type*} [Category* A'] [MonoidalCategory A']
    [(J.W (A := A')).IsMonoidal] [HasWeakSheafify J A'] {T : C} (hT : IsTerminal T) :
    letI := Sheaf.monoidalCategory J A'
    (ε (sheafToPresheaf J A')).app (Opposite.op T) =
      (constantSheafAdj J A' hT).unit.app (𝟙_ A') := by
  let := Sheaf.monoidalCategory J A'
  simp only [Adjunction.rightAdjointLaxMonoidal_ε]
  have hη : Functor.OplaxMonoidal.η (presheafToSheaf J A') = 𝟙 _ := rfl
  rw [Adjunction.homEquiv_unit, hη]
  simp [constantSheafAdj,
    Adjunction.comp_unit_app, constantPresheafAdj]
  rfl


end CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The pullback/restriction-of-scalars comparison, transposed along `p^* ⊣ p_*`, is
restriction of scalars of the unit of `p^* ⊣ p_*`.
Source: Stacks Project, Tag 03EK
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/
theorem upperStarRestrictScalarsIsoSheaf_hom_app_transpose
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (X : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).unit.app
        ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj X) ≫
      ((p)_*[ModuleCat.{u + 1} A]).map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app X) =
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p).unit.app X) := by
  apply ((Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).homEquiv _ _).injective
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p).comp
      (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)) X
  rw [Adjunction.comp_homEquiv] at h
  have hu (W : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).unit.app
          (((p)_*[ModuleCat.{u + 1} B]).obj W) =
        ((p)_*[ModuleCat.{u + 1} B]).map
          ((Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ).unit.app W) := rfl
  have e1 : (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).homEquiv _ _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).unit.app
        ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj X) ≫
      ((p)_*[ModuleCat.{u + 1} A]).map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app X)) =
      ((upperStarLowerStarAdjunction (ModuleCat B) p).comp
            (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)).unit.app X := by
    rw [← Adjunction.homEquiv_unit]
    exact h
  rw [e1, Adjunction.comp_unit_app, Adjunction.homEquiv_unit]
  erw [← hu]
  exact ((Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).unit.naturality _)


/-- The unit of the lax monoidal direct image `p_*`, on global sections, sends the unit
section to the unit section: in terms of the constant sheaf adjunctions at the terminal
objects of the two small étale sites.
Source: Stacks Project, Tag 03PW
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/
theorem constantSheafAdj_unit_comp_lowerStar_ε {B : Type (u + 1)} [CommRing B]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} B)
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).unit.app
        (ModuleCat.of B B) ≫
      (Functor.LaxMonoidal.ε ((p)_*[ModuleCat.{u + 1} B])).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) =
    (constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} B)
        (isTerminalOverPullbackObjMkId p)).unit.app (ModuleCat.of B B) := by
  have h1 := Sheaf.ε_sheafToPresheaf_app_eq_constantSheafAdj_unit (J := Y.smallEtaleTopology)
    (A' := ModuleCat.{u + 1} B) (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)
  have h2 := Sheaf.ε_sheafToPresheaf_app_eq_constantSheafAdj_unit (J := Z.smallEtaleTopology)
    (A' := ModuleCat.{u + 1} B) (isTerminalOverPullbackObjMkId p)
  have h3 := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @Etale ⊤ p) (ModuleCat.{u + 1} B)
    (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)
    (op (Scheme.Etale.mk (𝟙 Y)))
  erw [← h1, ← h2]
  exact h3


open MonoidalCategory in
/-- The adjoint transpose of the restricted-coefficient pullback square along `p^* ⊣ p_*`.
Source: Zheng Construction 2.26; Stacks 07A4
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/
theorem upperStarLowerStarAdjunction_unit_comp_restrictScalars
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).unit.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))) ≫
      ((p)_*[ModuleCat.{u + 1} A]).map
        ((upperStar (ModuleCat.{u + 1} A) p).map
          ((constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars φ)).inv.app
            (ModuleCat.of B B)) ≫
        (upperStarRestrictScalarsIsoSheaf φ p).hom.app _ ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).map
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) p)).symm.hom ≫
        (constantCommuteCompose Z.smallEtaleTopology (ModuleCat.restrictScalars φ)).hom.app
          (ModuleCat.of B B)) =
    (constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars φ)).inv.app
        (ModuleCat.of B B) ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        (Functor.LaxMonoidal.ε ((p)_*[ModuleCat.{u + 1} B])) ≫
      ((p)_*[ModuleCat.{u + 1} A]).map
        ((constantCommuteCompose Z.smallEtaleTopology (ModuleCat.restrictScalars φ)).hom.app
          (ModuleCat.of B B)) := by
  have hρ := upperStarRestrictScalarsIsoSheaf_hom_app_transpose φ p
    (𝟙_ (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)))
  have hη : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p).unit.app _ ≫
      ((p)_*[ModuleCat.{u + 1} B]).map
        (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) p)).symm.hom =
      Functor.LaxMonoidal.ε ((p)_*[ModuleCat.{u + 1} B]) := by
    rw [Iso.symm_hom, Functor.Monoidal.εIso_inv, Etale.upperStar_η, Functor.map_comp]
    erw [Adjunction.unit_naturality_assoc]
    rw [Adjunction.right_triangle_components]
    exact Category.comp_id _
  simp only [Functor.map_comp]
  have n := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).unit_naturality
    ((constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars φ)).inv.app
      (ModuleCat.of B B))
  erw [reassoc_of% n]
  congr 1
  erw [reassoc_of% hρ]
  rw [← hη, Functor.map_comp, Category.assoc]
  rfl


/-- The constant-sheaf pullback comparison on the restricted coefficient module `B` is the
composite of the constant-sheaf/restriction comparisons, the pullback/restriction comparison,
and the monoidal unit comparison of `p^*`. Both sides have the sectionwise identity as their
transpose along the constant sheaf and pullback adjunctions.
Source: Zheng Construction 2.26; Stacks 07A4 and 07A6
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback). -/
theorem constantSheafCompUpperStarIso_hom_app_restrictScalars
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (constantSheafCompUpperStarIso A p).hom.app
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)) =
      (upperStar (ModuleCat.{u + 1} A) p).map
          ((constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars φ)).inv.app
            (ModuleCat.of B B)) ≫
        (upperStarRestrictScalarsIsoSheaf φ p).hom.app _ ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).map
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) p)).symm.hom ≫
        (constantCommuteCompose Z.smallEtaleTopology (ModuleCat.restrictScalars φ)).hom.app
          (ModuleCat.of B B) := by
  have hσ := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)).ofNatIsoRight
        (NatIso.ofComponents (fun _ ↦ Iso.refl _)))
    (constantSheafAdj _ _ (isTerminalOverPullbackObjMkId p))
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hσ
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.comp_id] at hσ
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).homEquiv _ _).injective
  apply ((constantSheafAdj _ _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)).homEquiv _ _).injective
  erw [hσ]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [upperStarLowerStarAdjunction_unit_comp_restrictScalars φ p]
  have hKY := map_constantSheafAdj_unit_comp_constantCommuteCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars φ) (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)
    (ModuleCat.of B B)
  have hKZ := map_constantSheafAdj_unit_comp_constantCommuteCompose Z.smallEtaleTopology
    (ModuleCat.restrictScalars φ) (isTerminalOverPullbackObjMkId p) (ModuleCat.of B B)
  have hE := constantSheafAdj_unit_comp_lowerStar_ε (B := B) p
  have hi := congrArg (fun f ↦ f.hom.app (op (Scheme.Etale.mk (𝟙 Y))))
    ((constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars φ)).hom_inv_id_app
      (ModuleCat.of B B))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hi
  rw [← hKZ, ← hE, ← hKY]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hi]
  rfl


/-- The two canonical ways to pull back the restricted coefficient module agree.
Source: Zheng Construction 2.26; Stacks 07A4 and 07A6
(blueprint: lem-sfb-ordinary-exceptional-scalar-coefficient-pullback).

Proof: first work with sheaves. The restriction/pullback isomorphism is the unique
comparison of the two composites left adjoint to direct image followed by coextension.
The constant-sheaf comparison with restriction preserves the constant adjunction counit.
Apply the two composite adjunction Hom equivalences to the claimed square on the free
rank-one B-module. Both transposes are the sectionwise identity, so injectivity gives
the square. The monoidal unit comparison is its value on the free rank-one module:
its transpose is the lax direct-image unit, hence the same sectionwise identity.
Now apply the degree-zero single functor. Naturality of the exact derived/single
comparison and the composition comparison identifies the resulting square with the
one displayed here. Cancel the exact derived/single isomorphisms; this gives the
claimed equality with the actual chosen comparisons, including their units. -/
theorem ordinaryExceptional_scalarCoefficient_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
        (ordinaryScalarCoefficientIso φ Y).hom ≫
      ((constantFunctorCompLeftDerivedUpperStarIso A p).app
        (ordinaryCoefficientComplex φ)).hom =
      (scalarCoefficientPullbackIso φ p).hom ≫ (ordinaryScalarCoefficientIso φ Z).hom := by
  have h : (upperStar (ModuleCat.{u + 1} A) p).map
        ((constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars φ)).app
          (ModuleCat.of B B)).hom ≫
      (constantSheafCompUpperStarIso A p).hom.app
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)) =
      ((upperStarRestrictScalarsIsoSheaf φ p).app _ ≪≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapIso
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) p)).symm).hom ≫
      ((constantCommuteCompose Z.smallEtaleTopology (ModuleCat.restrictScalars φ)).app
          (ModuleCat.of B B)).hom := by
    rw [constantSheafCompUpperStarIso_hom_app_restrictScalars, Iso.app_hom,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have key := Functor.mapDerivedCategorySingleFunctor_constant_pullback_square
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) p)
    (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p)
    (constantSheafCompUpperStarIso A p)
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))
    ((constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars φ)).app
      (ModuleCat.of B B))
    ((constantCommuteCompose Z.smallEtaleTopology (ModuleCat.restrictScalars φ)).app
      (ModuleCat.of B B))
    ((upperStarRestrictScalarsIsoSheaf φ p).app _ ≪≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapIso
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) p)).symm) h
  simp only [ordinaryScalarCoefficientIso, constantFunctorCompLeftDerivedUpperStarIso,
    scalarCoefficientPullbackIso, exactSingleCoefficientIso]
  exact key

end AlgebraicGeometry.Etale
