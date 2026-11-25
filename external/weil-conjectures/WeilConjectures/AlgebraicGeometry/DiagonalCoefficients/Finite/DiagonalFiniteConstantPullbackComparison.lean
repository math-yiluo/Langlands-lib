/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteRealization
public import WeilConjectures.CategoryTheory.SixFunctors.CompIsoApp
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteSingleComparisonSquare

/-! # Finite constant pullback and degree-zero comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
-- The derived comparison APIs use the standard sheaf Abelian structure.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
section
attribute [local instance 100000] AlgebraicGeometry.Etale.ordinaryFiniteDerivedCategoryInstance
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  finiteUnitComparison

private theorem constant_adj_unit (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
      (Scheme.ProEt.isTerminalMkId X)).unit.app (𝟙_ (ModuleCat.{u + 1} A)) =
    (Functor.LaxMonoidal.ε
      (sheafToPresheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).app
        (op (Scheme.ProEt.mk (𝟙 X))) := by
  simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
  rw [Adjunction.homEquiv_unit]
  have he : Functor.OplaxMonoidal.η
      (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) = 𝟙 _ := rfl
  simp [he]
  rfl

private theorem etale_constant_adj_unit (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
      (Scheme.Etale.isTerminalMkId X)).unit.app (𝟙_ (ModuleCat.{u + 1} A)) =
    (Functor.LaxMonoidal.ε (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))).app (op (Scheme.Etale.mk (𝟙 X))) := by
  simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
  rw [Adjunction.homEquiv_unit]
  have he : Functor.OplaxMonoidal.η
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) = 𝟙 _ := rfl
  simp [he]
  rfl

private theorem constant_comparison_unit (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    (finiteConstantComparison A X).hom =
      Functor.OplaxMonoidal.η (comparisonUpperStar (ModuleCat.{u + 1} A) X) := by
  let C := ModuleCat.{u + 1} A
  let a := comparisonAdjunction C X
  let c := constantSheafAdj X.smallEtaleTopology C (Scheme.Etale.isTerminalMkId X)
  let d := constantSheafAdj (Scheme.ProEt.topology X) C (Scheme.ProEt.isTerminalMkId X)
  let e := (Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso C
    X.smallEtaleTopology (Scheme.ProEt.topology X) (op (Scheme.Etale.mk (𝟙 X)))
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((c.comp a).ofNatIsoRight e) d (𝟙_ C)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  erw [Equiv.trans_apply] at hh
  change c.homEquiv _ _ (a.homEquiv _ _ (finiteConstantComparison A X).hom) ≫ 𝟙 _ =
    d.unit.app (𝟙_ C) at hh
  rw [Category.comp_id] at hh
  apply (a.homEquiv _ _).injective
  apply (c.homEquiv _ _).injective
  have ha : a.homEquiv _ _
      (Functor.OplaxMonoidal.η (comparisonUpperStar C X)) =
      Functor.LaxMonoidal.ε (comparisonLowerStar C X) := by
    change a.unit.app (𝟙_ _) ≫ _ = _
    exact a.unit_app_unit_comp_map_η
  rw [hh]
  erw [ha]
  rw [Adjunction.homEquiv_unit]
  have hc : c.unit.app (𝟙_ C) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf X.smallEtaleTopology C)).app
        (op (Scheme.Etale.mk (𝟙 X))) :=
    etale_constant_adj_unit A X
  have hp : d.unit.app (𝟙_ C) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) C)).app
        (op (Scheme.ProEt.mk (𝟙 X))) := constant_adj_unit A X
  erw [hc, hp]
  exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (Scheme.toProEt X) C X.smallEtaleTopology (Scheme.ProEt.topology X)
      (op (Scheme.Etale.mk (𝟙 X)))).symm

private theorem ordinary_constant_pullback_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).map (finiteConstantComparison A Y).inv ≫
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        (Etale.ordinaryFiniteConstant A Y) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) ≫
      (finiteConstantComparison A X).hom =
    Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f) := by
  let C := ModuleCat.{u + 1} A
  let F := comparisonUpperStar C Y ⋙ upperStar C f
  let G := Etale.upperStar C f ⋙ comparisonUpperStar C X
  let e := comparisonUpperStarCompUpperStarIso C f
  have he : e.hom.app (𝟙_ _) ≫ Functor.OplaxMonoidal.η G =
      Functor.OplaxMonoidal.η F := by
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).1
    rw [← Category.assoc, NatTrans.IsMonoidal.unit (τ := e.hom)]
    exact (Functor.Monoidal.ε_η G).trans (Functor.Monoidal.ε_η F).symm
  have hi : (finiteConstantComparison A Y).inv =
      Functor.LaxMonoidal.ε (comparisonUpperStar C Y) := by
    apply (cancel_mono (finiteConstantComparison A Y).hom).1
    rw [Iso.inv_hom_id, constant_comparison_unit]
    exact (Functor.Monoidal.ε_η _).symm
  have ht : (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
      (ModuleCat.of A A) = Functor.OplaxMonoidal.η (Etale.upperStar C f) :=
    Etale.upperStarConstantSheafIso_hom_app_tensorUnit C f
  rw [hi, constant_comparison_unit, ht]
  change (upperStar C f).map (Functor.LaxMonoidal.ε (comparisonUpperStar C Y)) ≫
    e.hom.app (𝟙_ _) ≫ (comparisonUpperStar C X).map
      (Functor.OplaxMonoidal.η (Etale.upperStar C f)) ≫
        Functor.OplaxMonoidal.η (comparisonUpperStar C X) = _
  rw [← Functor.OplaxMonoidal.comp_η, he, Functor.OplaxMonoidal.comp_η]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.ε_η,
    CategoryTheory.Functor.map_id, Category.id_comp]

private theorem comp_iso_left_trans {C D E V : Type*}
    [Category C] [Category D] [Category E] [Category V]
    {S : C ⥤ D} {F G : D ⥤ V} {H : C ⥤ E} {I : E ⥤ V}
    (p : F ≅ G) (q : S ⋙ G ≅ H ⋙ I) (M : C) :
    (Functor.compIsoApp (Functor.isoWhiskerLeft S p ≪≫ q) M).hom =
      p.hom.app (S.obj M) ≫ (Functor.compIsoApp q M).hom := by
  unfold Functor.compIsoApp
  rfl

private theorem ordinary_single_constant (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    (Etale.ordinaryFiniteSingleFunctor A X).obj (Etale.ordinaryFiniteConstant A X) =
      Etale.ordinaryFiniteUnit A X := rfl

private theorem unit_pullback_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (geoP1UnitPullback A f).hom =
      (geoP1PullComparison A f).hom.app (Etale.ordinaryFiniteUnit A Y) ≫
        (geoP1Comparison A X).map (Etale.ordinaryFiniteUnitPullback A f).hom := by
  rfl

private theorem pull_comparison_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (geoP1PullComparison A f).hom.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        ((geoP1Comparison A Y).obj K) ≫
      (Functor.mapDerivedCategoryCompIso (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
        (upperStar (ModuleCat.{u + 1} A) f)).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f)).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso (Etale.upperStar (ModuleCat.{u + 1} A) f)
        (comparisonUpperStar (ModuleCat.{u + 1} A) X)).inv.app K ≫
      (geoP1Comparison A X).map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).inv.app K) := by
  rfl

private theorem proetale_single_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :
    (Functor.compIsoApp
      (ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f) M).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (Functor.compIsoApp
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0) M).hom := by
  exact comp_iso_left_trans _ _ M

private theorem ordinary_unit_hom_cached (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.ordinaryFiniteUnitPullback A f).hom =
      (Functor.compIsoApp (Etale.ordinaryFiniteSinglePullbackIso A f)
        (Etale.ordinaryFiniteConstant A Y)).hom ≫
      (Etale.ordinaryFiniteSingleFunctor A X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) := by
  unfold Etale.ordinaryFiniteUnitPullback Functor.compIsoApp
  rfl

private theorem finite_unit_comparison_hom (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    (finiteUnitComparison A X).hom =
      (Functor.compIsoApp (finiteSingleComparison A X)
        (Etale.ordinaryFiniteConstant A X)).hom ≫
      (DerivedCategory.singleFunctor _ 0).map (finiteConstantComparison A X).hom := by
  unfold finiteUnitComparison
  rw [Iso.trans_hom, Functor.mapIso_hom]

private theorem finite_constant_pullback_raw (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ho : (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
    (Etale.ordinaryFiniteConstant A Y) ≫ (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app (ModuleCat.of A A)) ≫
    (finiteConstantComparison A X).hom =
      (upperStar (ModuleCat.{u + 1} A) f).map (finiteConstantComparison A Y).hom ≫
        Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f)) :
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
      ((Etale.ordinaryFiniteSingleFunctor A Y).obj (Etale.ordinaryFiniteConstant A Y))) ≫
    (Functor.mapDerivedCategoryCompIso (comparisonUpperStar (ModuleCat.{u + 1} A) Y) (upperStar
      (ModuleCat.{u + 1} A) f)).hom.app ((Etale.ordinaryFiniteSingleFunctor A Y).obj
      (Etale.ordinaryFiniteConstant A Y)) ≫
    (Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A)
      f)).hom.app ((Etale.ordinaryFiniteSingleFunctor A Y).obj (Etale.ordinaryFiniteConstant A Y)) ≫
    (Functor.mapDerivedCategoryCompIso (Etale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)).inv.app ((Etale.ordinaryFiniteSingleFunctor A
      Y).obj (Etale.ordinaryFiniteConstant A Y)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv.app
      ((Etale.ordinaryFiniteSingleFunctor A Y).obj (Etale.ordinaryFiniteConstant A Y))) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
    ((Functor.compIsoApp (Functor.isoWhiskerLeft (Etale.ordinaryFiniteSingleFunctor A Y)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
      (Etale.ordinaryFiniteSingleExactPullbackIso A f)) (Etale.ordinaryFiniteConstant A Y)).hom ≫
      (Etale.ordinaryFiniteSingleFunctor A X).map ((Scheme.upperStarConstantSheafIso (ModuleCat.{u +
      1} A) f).hom.app (ModuleCat.of A A))) ≫
    (Functor.compIsoApp (finiteSingleComparison A X) (Etale.ordinaryFiniteConstant A X)).hom ≫
      (DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).map
      (finiteConstantComparison A X).hom =
    (geoP1Pullback A f).map ((Functor.compIsoApp (finiteSingleComparison A Y)
      (Etale.ordinaryFiniteConstant A Y)).hom ≫
    (DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).map
      (finiteConstantComparison A Y).hom) ≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
      ((DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
      (geoCartierConstant A Y)) ≫
    (Functor.compIsoApp ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0)
      (geoCartierConstant A Y)).hom ≫
    (DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).map
      (Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f)) := by
  exact finite_single_comparison_square A f (Etale.ordinaryFiniteConstant A Y)
    (finiteConstantComparison A Y) (finiteConstantComparison A X)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app (ModuleCat.of A A))
    (Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f)) ho

/-- The finite unit comparison intertwines the canonical constant pullback with
its degree-zero pro-etale pullback. Source: diagonal tower coefficient changes (1),
the constant coefficient unit and the etale/pro-etale inverse-image square.
(blueprint: lem-diagonal-finite-constant-pullback-comparison).

Proof: the regular module is the tensor unit. Uniqueness of the constant-sheaf
left adjoint identifies its comparison with the oplax monoidal unit. The etale
constant pullback is the corresponding unit map as well. Monoidality of the
comparison square therefore gives the ordinary constant pullback square.
Naturality of the exact-derived single-object comparisons, their compatibility
with composition and natural isomorphisms, and cancellation of the left-derived
comparison isomorphisms lift that square to the displayed derived equality.
The argument uses no nontriviality or nonemptiness hypothesis. -/
theorem finite_constant_pullback_comparison (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (geoP1UnitPullback A f).hom ≫ (finiteUnitComparison A X).hom =
      (geoP1Pullback A f).map (finiteUnitComparison A Y).hom ≫
        (Functor.compIsoApp
          (ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f)
          (geoCartierConstant A Y)).hom ≫
        (DerivedCategory.singleFunctor _ 0).map
          (Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f)) := by
  have ho : (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
    (Etale.ordinaryFiniteConstant A Y) ≫ (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app (ModuleCat.of A A)) ≫
    (finiteConstantComparison A X).hom =
      (upperStar (ModuleCat.{u + 1} A) f).map (finiteConstantComparison A Y).hom ≫
        Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) f) := by
    apply (cancel_epi ((upperStar (ModuleCat.{u + 1} A) f).map (finiteConstantComparison A
      Y).inv)).1
    rw [ordinary_constant_pullback_unit]
    simp only [← (upperStar (ModuleCat.{u + 1} A) f).map_comp_assoc, Iso.inv_hom_id, (upperStar
      (ModuleCat.{u + 1} A) f).map_id, Category.id_comp]
  have ht := finite_constant_pullback_raw A f ho
  with_reducible
    simpa only [unit_pullback_hom, pull_comparison_hom, finite_unit_comparison_hom,
      ordinary_unit_hom_cached, proetale_single_hom, Etale.ordinaryFiniteSinglePullbackIso,
      geoP1Comparison, geoP1Pullback, Functor.comp_obj, ordinary_single_constant,
      Category.assoc] using ht

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

end
