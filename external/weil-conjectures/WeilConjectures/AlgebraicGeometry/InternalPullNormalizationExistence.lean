/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Existence of normalized internal scalar pullback comparisons

The two composite scalar/geometric functors are compared by their universal
K-flat computation counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

private theorem pull_preserves_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules Λ Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) := by
  have : (Mod.extendScalars (condensedPullbackHom Λ f)).IsEquivalence := by
    have : (Mod.comap (asIso (condensedPullbackHom Λ f)).inv).IsEquivalence :=
      (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).symm
        |>.isEquivalence_functor
    exact Functor.isEquivalence_of_iso
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm
  exact ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (CondensedRing.upperStar Λ f))
      (.up ℤ)).app P)
    ((Mod.extendScalars (condensedPullbackHom Λ f))
      |>.kFlat_mapHomologicalComplex_obj_of_isEquivalence
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
          |>.kFlat_mapHomologicalComplex_obj P hP))

private def compositePullCounit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ (D a Y ⋙ L Λ' f) ⟶
      (extension a Y).mapHomotopyCategory (.up ℤ) ⋙
      (CondensedRing.upperStar Λ' f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (scalarCounit a Y) (L Λ' f) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((extension a Y).mapHomotopyCategory (.up ℤ))
      (pullCounit (Λ := Λ') f)

private def compositeScalarCounit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ (L Λ f ⋙ D a X) ⟶
      (CondensedRing.upperStar Λ f ⋙ extension a X).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullCounit (Λ := Λ) f) (D a X) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ))
      (scalarCounit a X) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (CondensedRing.upperStar Λ f ⋙ extension a X)) (.up ℤ)).hom
      DerivedCategory.Qh

/-- A normalized scalar/geometric pullback comparison exists for every morphism.
(1);
Stacks Tags 0D6D, 0G7E, 07A6 (auxiliary; not a blueprint node).
Proof: compare the two composite ordinary pullback functors by the specified coefficient
pullback isomorphism, construct both derived counits, and apply the K-flat universal
characterization. Geometric pullback preserves K-flat complexes; cancellation of the
counits gives exactly `PullNormalized`. -/
theorem internal_pull_normalization_exists (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X, PullNormalized a f b := by
  have hc : (D a Y ⋙ L Λ' f).IsLeftDerivedFunctor (compositePullCounit a f)
      (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)) := by
    apply (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
        (compositePullCounit a f) ?_
    intro P
    have hs : IsIso ((scalarCounit a Y).app P.obj) := by
      unfold scalarCounit D
      dsimp only [id]
      exact (extension a Y).derives_kFlat.isIso_of_isLeftDerivedFunctor
        (extension a Y).leftDerivedFunctorCounit P
    have hg : IsIso (pullCounit (Λ := Λ') f) := by
      unfold pullCounit L CondensedRing.moduleObjectDerivedPullback
      dsimp only [id]
      exact Functor.isIso_leftDerivedFunctorCounit (CondensedRing.upperStar Λ' f)
    have hgs : IsIso ((pullCounit (Λ := Λ') f).app
        (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P.obj)) :=
      NatIso.isIso_app_of_isIso _ _
    have hss : IsIso ((L Λ' f).map ((scalarCounit a Y).app P.obj)) :=
      Functor.map_isIso _ _
    change IsIso (𝟙 _ ≫ (L Λ' f).map ((scalarCounit a Y).app P.obj) ≫
      𝟙 _ ≫ (pullCounit (Λ := Λ') f).app
        (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P.obj))
    infer_instance
  have hd : (L Λ f ⋙ D a X).IsLeftDerivedFunctor (compositeScalarCounit a f)
      (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)) := by
    apply (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
        (compositeScalarCounit a f) ?_
    intro P
    obtain ⟨P, hP⟩ := P
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    have hs : IsIso ((scalarCounit a X).app
        (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P))) := by
      unfold scalarCounit D
      dsimp only [id]
      exact (extension a X).isIso_leftDerivedFunctorCounit_app_of_kFlat _
        (pull_preserves_kFlat f P ((HomotopyCategory.kFlat_quotient_obj_iff P).1 hP))
    have hg : IsIso (pullCounit (Λ := Λ) f) := by
      unfold pullCounit L CondensedRing.moduleObjectDerivedPullback
      dsimp only [id]
      exact Functor.isIso_leftDerivedFunctorCounit (CondensedRing.upperStar Λ f)
    have hgs : IsIso ((pullCounit (Λ := Λ) f).app
        ((HomotopyCategory.quotient _ _).obj P)) := NatIso.isIso_app_of_isIso _ _
    have hss : IsIso ((D a X).map ((pullCounit (Λ := Λ) f).app
        ((HomotopyCategory.quotient _ _).obj P))) := Functor.map_isIso _ _
    change IsIso (𝟙 _ ≫ (D a X).map ((pullCounit (Λ := Λ) f).app
        ((HomotopyCategory.quotient _ _).obj P)) ≫ 𝟙 _ ≫
      (scalarCounit a X).app (((CondensedRing.upperStar Λ f).mapHomotopyCategory
        (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (CondensedRing.upperStar Λ f ⋙ extension a X)) (.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P)))
    infer_instance
  let e := Functor.isoWhiskerRight
    (Functor.mapHomotopyCategoryCompIso (CondensedRing.pullIso a f).symm (.up ℤ))
    DerivedCategory.Qh
  let b := Functor.leftDerivedNatIso (D a Y ⋙ L Λ' f) (L Λ f ⋙ D a X)
    (compositePullCounit a f) (compositeScalarCounit a f)
    (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)) e
  refine ⟨b, ?_⟩
  intro P
  have h := Functor.leftDerivedNatTrans_app (D a Y ⋙ L Λ' f) (L Λ f ⋙ D a X)
    (compositePullCounit a f) (compositeScalarCounit a f)
    (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)) e.hom P
  simpa only [b, Functor.leftDerivedNatIso_hom, compositePullCounit,
    compositeScalarCounit, e, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.assoc] using h

end AlgebraicGeometry.ProEtale.QuotientChange
