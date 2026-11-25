/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Intrinsic proper/open arrows for varying rings

Source: Stacks Project, Tags 0F7B, 03DI and 09AE, and the explicit lift/projection
construction in the blueprint (blueprint: def-sp-varying-ring-proper-open-arrows).

All intrinsic maps are first constructed on module systems, then localized termwise.
Their derived proper/open comparison is the specified ordinary adjunction mate.

## Main definitions

- `moduleBeta`, `modulePi`: the intrinsic open comparison and clopen projection.
- `moduleAlpha`, `alpha`, `gamma`: the actual system arrow, its localization and mate.
- `constantGamma`: the arbitrary constant-ring comparison from the strict-tower calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The square comparison is uniquely fixed by the explicit compositor formula.
Source: Stacks, Tag 07A7 (blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: the displayed composite is a witness, and its defining equality gives uniqueness. -/
theorem moduleSquareG_existsUnique {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    ∃! e : pull R φ i ⋙ pull R φ r ≅ pull R φ p ⋙ pull R φ k,
      e = (moduleGComp R φ r i).symm ≪≫ eqToIso (congrArg (pull R φ) h.symm) ≪≫
        moduleGComp R φ k p := by
  exact ⟨_, rfl, fun _ he ↦ he⟩

/-- Canonical comparison of the two iterated inverse images around any commutative square.
Source: Stacks, Tag 07A7 (blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    pull R φ i ⋙ pull R φ r ≅ pull R φ p ⋙ pull R φ k :=
  (moduleSquareG_existsUnique R φ k r p i h).choose

/-- The square comparison retains exactly its original compositor formula.
Source: Stacks, Tag 07A7 (blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: this is the defining equality of the uniquely specified comparison. -/
theorem moduleSquareG_eq {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    moduleSquareG R φ k r p i h =
      (moduleGComp R φ r i).symm ≪≫ eqToIso (congrArg (pull R φ) h.symm) ≪≫
        moduleGComp R φ k p :=
  (moduleSquareG_existsUnique R φ k r p i h).choose_spec.1

/-- The inverse cartesian open comparison is defined by precisely the open-unit transpose.
Source: Stacks, Tags 09AE and 07A7
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleBetaInvApp {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M : Modules R φ U) :
    (extension R φ j').obj ((pull R φ gU).obj M) ⟶ (pull R φ g).obj ((extension R φ j).obj M) :=
  ((moduleJAdj R φ j').homEquiv _ _).symm
    ((pull R φ gU).map ((moduleJAdj R φ j).unit.app M) ≫
      (moduleSquareG R φ gU j' j g h).inv.app ((extension R φ j).obj M))

/-- Naturality of the specified open-unit transpose. Source: Stacks, Tag 09AE
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: use naturality of the open unit, the pullback compositor and the adjunction
Hom equivalence. The transposes of both sides are the same naturality square. -/
theorem moduleBetaInvApp_naturality {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M N : Modules R φ U) (f : M ⟶ N) :
    (pull R φ gU ⋙ extension R φ j').map f ≫ moduleBetaInvApp R φ gU j' j g h N =
      moduleBetaInvApp R φ gU j' j g h M ≫ (extension R φ j ⋙ pull R φ g).map f := by
  unfold moduleBetaInvApp
  apply (moduleJAdj R φ j').homEquiv_naturality_right_square
  have hu := (moduleJAdj R φ j).unit.naturality f
  change f ≫ (moduleJAdj R φ j).unit.app N =
    (moduleJAdj R φ j).unit.app M ≫
      (pull R φ j).map ((extension R φ j).map f) at hu
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  have hn := (moduleSquareG R φ gU j' j g h).inv.naturality ((extension R φ j).map f)
  simp only [Functor.comp_map] at hn ⊢
  rw [hn]

/-- The inverse comparison as a natural transformation with the specified transpose.
Source: Stacks, Tag 09AE (blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleBetaInv {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g) :
    pull R φ gU ⋙ extension R φ j' ⟶ extension R φ j ⋙ pull R φ g where
  app := moduleBetaInvApp R φ gU j' j g h
  naturality := moduleBetaInvApp_naturality R φ gU j' j g h

private theorem level_derived_open_unit_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : IsIso (levelJAdj R j n).unit := by
  let B := R n
  let D := StrictTower.ConstantNormalization.delta B U
  let E := StrictTower.ev B U 0
  let L := (StrictTower.moduleJ B j).mapDerivedCategory
  let F := (StrictTower.modulePullback B j).mapDerivedCategory
  have := StrictTower.jAdj_unit_isIso B j
  let e : L ⋙ F ≅ 𝟭 (DerivedCategory (StrictTower.Modules B U)) :=
    (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (StrictTower.ConstantNormalization.deltaEval B U 0).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D
      ((Functor.associator E L F).symm ≪≫
        Functor.isoWhiskerRight (StrictTower.evalJ B j 0).symm F ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (StrictTower.J B j) (StrictTower.evalG B j 0).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso (StrictTower.jAdj B j).unit).symm E ≪≫
        Functor.leftUnitor E) ≪≫
    StrictTower.ConstantNormalization.deltaEval B U 0
  exact (levelJAdj R j n).isIso_unit_of_iso e

private theorem derived_open_unit_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (jAdj R φ j).unit := by
  have hi (M : Derived R φ U) : IsIso ((jAdj R φ j).unit.app M) := by
    let d := (WeilConjectures.SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
      (Scheme.ProEt.topology U) (coefficients R U) (coefficientTransition R φ U)).some
    apply d.systems.detects
    intro n
    have := level_derived_open_unit_iso R j n
    have := evalJInv_isIso R φ j n
    have hu := unit_mateEquiv_symm (jAdj R φ j) (levelJAdj R j n)
      (evalG R φ j n).hom M
    have : IsIso ((ev R φ U n).map ((jAdj R φ j).unit.app M) ≫
        (evalG R φ j n).hom.app ((J R φ j).obj M)) := by
      rw [hu]
      change IsIso ((levelJAdj R j n).unit.app ((ev R φ U n).obj M) ≫
        (StrictTower.modulePullback (R n) j).mapDerivedCategory.map
          ((evalJInv R φ j n).app M))
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((evalG R φ j n).hom.app ((J R φ j).obj M))
  exact NatIso.isIso_of_isIso_app _

/-- The open-extension unit is invertible. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: on an object lying over the open there is exactly one lift to it, so restriction
of the extension presheaf is the original module. This survives sheafification,
termwise extension to strict towers, and exact localization. -/
theorem moduleJAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (moduleJAdj R φ j).unit := by
  have := derived_open_unit_iso R φ j
  let F := extension R φ j ⋙ pull R φ j
  let e : F.mapDerivedCategory ≅ 𝟭 (Derived R φ U) :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ (asIso (jAdj R φ j).unit).symm
  let h := DerivedCategory.homologyFunctor (Modules R φ U) 0
  let t : F ≅ 𝟭 (Modules R φ U) :=
    (Functor.rightUnitor F).symm ≪≫
      Functor.isoWhiskerLeft F
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R φ U) 0).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapDerivedCategorySingleFunctor 0).symm h ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight e h ≪≫ Functor.leftUnitor h) ≪≫
      DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R φ U) 0
  exact (moduleJAdj R φ j).isIso_unit_of_iso t

private theorem level_basechange_image (B : Type (u + 1)) [CommRing B]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (hsq : IsPullback a j' j g)
    (M : DerivedCategory (StrictTower.Modules B U)) :
    Nonempty ((StrictTower.modulePullback B g).mapDerivedCategory.obj
      ((StrictTower.moduleJ B j).mapDerivedCategory.obj M) ≅
      (StrictTower.moduleJ B j').mapDerivedCategory.obj
        ((StrictTower.modulePullback B a).mapDerivedCategory.obj M)) := by
  let D := StrictTower.ConstantNormalization.delta B U
  let E := StrictTower.ev B X' 0
  let L := (StrictTower.moduleJ B j).mapDerivedCategory
  let L' := (StrictTower.moduleJ B j').mapDerivedCategory
  let F := (StrictTower.modulePullback B g).mapDerivedCategory
  let F' := (StrictTower.modulePullback B a).mapDerivedCategory
  let e := (StrictTower.ConstantNormalization.deltaEval B U 0).app M
  exact ⟨F.mapIso (L.mapIso e.symm ≪≫ (StrictTower.evalJ B j 0).symm.app (D.obj M)) ≪≫
    (StrictTower.evalG B g 0).symm.app ((StrictTower.J B j).obj (D.obj M)) ≪≫
    E.mapIso ((StrictTower.beta B a j' j g h hsq).app (D.obj M)) ≪≫
    (StrictTower.evalJ B j' 0).app ((StrictTower.G B a).obj (D.obj M)) ≪≫
    L'.mapIso ((StrictTower.evalG B a 0).app (D.obj M) ≪≫ F'.mapIso e)⟩

private theorem derived_basechange_counit {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (M : Derived R φ U) :
    IsIso ((jAdj R φ j').counit.app ((G R φ g).obj ((J R φ j).obj M))) := by
  let N := (G R φ g).obj ((J R φ j).obj M)
  let d := (WeilConjectures.SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X') (coefficients R X') (coefficientTransition R φ X')).some
  apply d.systems.detects
  intro n
  have := level_derived_open_unit_iso R j' n
  let ff := (levelJAdj R j' n).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  obtain ⟨e⟩ := level_basechange_image (R n) a j' j g h hsq ((ev R φ U n).obj M)
  let t := (evalG R φ g n).app ((J R φ j).obj M) ≪≫
    (StrictTower.modulePullback (R n) g).mapDerivedCategory.mapIso ((evalJ R φ j n).app M) ≪≫ e
  have : IsIso ((levelJAdj R j' n).counit.app ((ev R φ X' n).obj N)) :=
    (levelJAdj R j' n).isIso_counit_app_of_iso t
  have := evalJInv_isIso R φ j' n
  have hc := mateEquiv_counit_symm (jAdj R φ j') (levelJAdj R j' n)
    (evalG R φ j' n).hom N
  have : IsIso ((evalJInv R φ j' n).app ((G R φ j').obj N) ≫
      (ev R φ X' n).map ((jAdj R φ j').counit.app N)) := by
    rw [show (evalJInv R φ j' n).app _ =
      ((mateEquiv (jAdj R φ j') (levelJAdj R j' n)).symm
        (evalG R φ j' n).hom).app _ from rfl, ← hc]
    infer_instance
  exact IsIso.of_isIso_comp_left ((evalJInv R φ j' n).app _) _

private theorem ordinary_open_image {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : Modules R φ X)
    [IsIso ((jAdj R φ j).counit.app ((DerivedCategory.singleFunctor _ 0).obj N))] :
    Nonempty (N ≅ (extension R φ j).obj ((pull R φ j).obj N)) := by
  let H := DerivedCategory.homologyFunctor (Modules R φ X) 0
  let e := ((extension R φ j).mapDerivedCategorySingleFunctor 0).symm.app
      ((pull R φ j).obj N) ≪≫
    (J R φ j).mapIso (((pull R φ j).mapDerivedCategorySingleFunctor 0).symm.app N) ≪≫
    asIso ((jAdj R φ j).counit.app ((DerivedCategory.singleFunctor _ 0).obj N))
  exact ⟨(DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R φ X) 0).symm.app N ≪≫
    H.mapIso e.symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R φ X) 0).app _⟩

/-- The unit-normalized comparison is invertible for a cartesian open square and
arbitrary rings. Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: restriction commutes with direct image on the same pulled-back test object.
The two routes are left adjoint to these canonically identified right adjoints.
Their unique unit-preserving comparison is invertible and its inverse has exactly
the displayed transpose. The equalities descend from strict complexes. -/
theorem moduleBetaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (moduleBetaInv R φ gU j' j g h) := by
  have := moduleJAdj_unit_isIso R φ j
  have := moduleJAdj_unit_isIso R φ j'
  let ff := (moduleJAdj R φ j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hi (M : Modules R φ U) : IsIso ((moduleBetaInv R φ gU j' j g h).app M) := by
    let N := (pull R φ g).obj ((extension R φ j).obj M)
    let e := ((pull R φ g).mapDerivedCategorySingleFunctor 0).symm.app
        ((extension R φ j).obj M) ≪≫
      (G R φ g).mapIso (((extension R φ j).mapDerivedCategorySingleFunctor 0).symm.app M)
    have : IsIso ((jAdj R φ j').counit.app ((DerivedCategory.singleFunctor _ 0).obj N)) :=
      (NatTrans.isIso_app_iff_of_iso (jAdj R φ j').counit e).mpr
        (derived_basechange_counit R φ gU j' j g h hsq
          ((DerivedCategory.singleFunctor _ 0).obj M))
    obtain ⟨t⟩ := ordinary_open_image R φ j' N
    have := (moduleJAdj R φ j').isIso_counit_app_of_iso t
    change IsIso (moduleBetaInvApp R φ gU j' j g h M)
    unfold moduleBetaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Cartesian open base change, oriented as G_g j_! → j'_! G_gU.
Source: Stacks, Tag 09AE (blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleBeta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : extension R φ j ⋙ pull R φ g ≅ pull R φ gU ⋙ extension R φ j' :=
  (@asIso _ _ _ _ (moduleBetaInv R φ gU j' j g h)
    (moduleBetaInv_isIso R φ gU j' j g h hsq)).symm

/-- The canonical map from open extension to direct image is the counit mate of the
inverse open unit. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleOpenToP {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension R φ j ⟶ push R φ j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (extension R φ j) (moduleAdj R φ j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (@inv _ _ _ _ (moduleJAdj R φ j).unit (moduleJAdj_unit_isIso R φ j)) (push R φ j) ≫
          (Functor.leftUnitor _).hom

private theorem level_clopen_iso (B : Type (u + 1)) [CommRing B]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] :
    Nonempty ((StrictTower.moduleJ B j).mapDerivedCategory ≅
      (StrictTower.moduleDirectImage B j).rightDerivedFunctor) := by
  let D := StrictTower.ConstantNormalization.delta B U
  let E := StrictTower.ev B X 0
  let L := (StrictTower.moduleJ B j).mapDerivedCategory
  let P := (StrictTower.moduleDirectImage B j).rightDerivedFunctor
  have := StrictTower.openToR_isIso B j
  have := StrictTower.evalR_isIso B j 0
  exact ⟨(Functor.leftUnitor L).symm ≪≫
    Functor.isoWhiskerRight (StrictTower.ConstantNormalization.deltaEval B U 0).symm L ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D (StrictTower.evalJ B j 0).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft D (asIso (StrictTower.openToR B j))) E ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D (asIso (StrictTower.evalR B j 0)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (StrictTower.ConstantNormalization.deltaEval B U 0) P ≪≫
    Functor.leftUnitor P⟩

set_option backward.isDefEq.respectTransparency false in
private theorem derived_clopen_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] (M : Derived R φ U) :
    IsIso ((adj R φ j).unit.app ((J R φ j).obj M)) := by
  let d := (WeilConjectures.SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)).some
  apply d.systems.detects
  intro n
  obtain ⟨e⟩ := level_clopen_iso (R n) j
  have := level_derived_open_unit_iso R j n
  let ff := (levelJAdj R j n).fullyFaithfulLOfIsIsoUnit
  let fp := ff.ofIso e
  have : (Scheme.proEtaleRingModuleDirectImage j (coefficients R X n)
    (coefficients R U n) (StrictTower.constantRingIso (R n) j)).rightDerivedFunctor.Full := fp.full
  have : (Scheme.proEtaleRingModuleDirectImage j (coefficients R X n)
    (coefficients R U n) (StrictTower.constantRingIso (R n) j)).rightDerivedFunctor.Faithful :=
      fp.faithful
  let t := (evalJ R φ j n).app M ≪≫ e.app ((ev R φ U n).obj M)
  have : IsIso ((levelAdj R j n).unit.app ((ev R φ X n).obj ((J R φ j).obj M))) :=
    (levelAdj R j n).isIso_unit_app_of_iso t
  have := evalPMate_isIso R φ j n
  have hu := unit_mateEquiv (adj R φ j) (levelAdj R j n)
    (evalG R φ j n).inv ((J R φ j).obj M)
  have : IsIso ((ev R φ X n).map ((adj R φ j).unit.app ((J R φ j).obj M)) ≫
      (evalPMate R φ j n).app ((G R φ j).obj ((J R φ j).obj M))) := by
    rw [show (evalPMate R φ j n).app _ =
      (mateEquiv (adj R φ j) (levelAdj R j n) (evalG R φ j n).inv).app _ from rfl]
    rw [hu]
    change IsIso ((levelAdj R j n).unit.app ((ev R φ X n).obj ((J R φ j).obj M)) ≫
      (StrictTower.moduleDirectImage (R n) j).rightDerivedFunctor.map
        ((evalG R φ j n).inv.app ((J R φ j).obj M)))
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((evalPMate R φ j n).app _)

private theorem derived_clopen_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] : Nonempty (J R φ j ≅ P R φ j) := by
  have := derived_open_unit_iso R φ j
  let b := Functor.whiskerLeft (J R φ j) (adj R φ j).unit
  have hi (M : Derived R φ U) : IsIso (b.app M) := derived_clopen_unit R φ j M
  have : IsIso b := NatIso.isIso_of_isIso_app _
  exact ⟨(Functor.rightUnitor _).symm ≪≫ asIso b ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (jAdj R φ j).unit).symm (P R φ j) ≪≫
    Functor.leftUnitor _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_clopen_iso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] :
    Nonempty (extension R φ j ≅ push R φ j) := by
  obtain ⟨e⟩ := derived_clopen_iso R φ j
  let d := (WeilConjectures.SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology U) (coefficients R U) (coefficientTransition R φ U)).some
  have : IsGrothendieckAbelian.{u + 1} (Modules R φ U) := d.systems.grothendieck
  let F := push R φ j
  let H := DerivedCategory.homologyFunctor (Modules R φ X) 0
  let S := DerivedCategory.singleFunctor (Modules R φ U) 0
  let S' := DerivedCategory.Plus.singleFunctor (Modules R φ U) 0
  let I := DerivedCategory.Plus.ι (C := Modules R φ U)
  let I' := DerivedCategory.Plus.ι (C := Modules R φ X)
  let h : S ⋙ P R φ j ⋙ H ≅ F :=
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso (Modules R φ U) 0).symm
      (P R φ j ⋙ H) ≪≫
    Functor.associator S' I (P R φ j ⋙ H) ≪≫
    Functor.isoWhiskerLeft S'
      ((Functor.associator I (P R φ j) H).symm ≪≫
        Functor.isoWhiskerRight F.rightDerivedFunctorPlusCompatibility.symm H ≪≫
        Functor.associator F.rightDerivedFunctorPlus I' H) ≪≫
    F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
    F.rightDerivedZeroIsoSelf
  exact ⟨(Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (extension R φ j)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules R φ X) 0).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((extension R φ j).mapDerivedCategorySingleFunctor 0).symm H ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft S
      (Functor.isoWhiskerRight e H) ≪≫ h⟩

/-- For a clopen immersion the canonical open-to-direct-image comparison is invertible.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: over each pro-etale test object split sections into the product of sections on
the inverse image of the clopen image and on its complement. Both extension and direct
image give the first factor with zero second factor. The specified comparison is the
identity on the first factor. The same formula acts termwise on towers and complexes. -/
theorem moduleOpenToP_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (moduleOpenToP R φ j) := by
  obtain ⟨e⟩ := ordinary_clopen_iso R φ j
  have := moduleJAdj_unit_isIso R φ j
  let ff := (moduleJAdj R φ j).fullyFaithfulLOfIsIsoUnit
  let fp := ff.ofIso e
  have := fp.full
  have := fp.faithful
  have hi (M : Modules R φ U) : IsIso ((moduleOpenToP R φ j).app M) := by
    have := (moduleAdj R φ j).isIso_unit_app_of_iso (e.app M)
    dsimp only [moduleOpenToP, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The intrinsic clopen component projection, with no arbitrary splitting choice.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def modulePi {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : 𝟭 (Modules R φ X) ⟶ pull R φ s ⋙ extension R φ s :=
  (moduleAdj R φ s).unit ≫ Functor.whiskerLeft (pull R φ s)
    (@inv _ _ _ _ (moduleOpenToP R φ s) (moduleOpenToP_isIso R φ s))

/-- Equality transport for open extension, independent of proof-irrelevant instances.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-proper-open-arrows).
Proof: substitute the equality of scheme maps; proof irrelevance identifies the
open-immersion instances and hence the chosen universal-property functors. -/
theorem moduleJ_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    extension R φ f = extension R φ g := by
  subst g
  rfl

/-- The canonical equality transport for ordinary extension by zero.
Source: Stacks 03DI (blueprint: def-sp-varying-ring-proper-open-arrows). -/
def moduleJCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :=
  eqToIso (moduleJ_congr R φ h)

/-- The normalized non-cartesian open comparison uses moduleBeta and the intrinsic clopen
projection, followed by the open and pullback compositors. Source: Stacks, Tag 0F7B
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
noncomputable def moduleAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : extension R φ i ⋙ pull R φ p ⟶ pull R φ r ⋙ extension R φ k :=
  (moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (pull R φ (pullback.snd p i))
    (modulePi R φ (StrictTower.squareLift k r p i h))) (extension R φ (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (pull R φ (pullback.snd p i)) (pull R φ (StrictTower.squareLift k r p i h))
      (extension R φ (StrictTower.squareLift k r p i h))).inv (extension R φ (pullback.fst p i)) ≫
  (Functor.associator (pull R φ (pullback.snd p i) ⋙ pull R φ (StrictTower.squareLift k r p i h))
    (extension R φ (StrictTower.squareLift k r p i h)) (extension R φ (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (pull R φ (pullback.snd p i) ⋙ pull R φ (StrictTower.squareLift k r p i h))
    ((moduleJComp R φ (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (moduleJCongr R φ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((moduleGComp R φ (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (pull R φ) (pullback.lift_snd k r h))).hom) (extension R φ k)

/-- The intrinsic derived arrow is the localization of the constructed system map.
Source: Stacks 0F7B; Zheng 4.1
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : J R φ i ⋙ G R φ p ⟶ G R φ r ⋙ J R φ k :=
  (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules R φ S) (.up ℤ)) _ _
      (extension R φ i ⋙ pull R φ p).mapDerivedCategory
      (pull R φ r ⋙ extension R φ k).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (moduleAlpha R φ k r p i h) (.up ℤ))
          DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso _ _).inv

/-- The normalized proper/open map is exactly the unit-square-counit mate.
Source: Stacks 0F7B, 07A7
(blueprint: def-sp-varying-ring-proper-open-arrows). -/
def gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : P R φ r ⋙ J R φ i ⟶ J R φ k ⋙ P R φ p :=
  mateEquiv (adj R φ r) (adj R φ p) (alpha R φ k r p i h)

/-- Embed a single coefficient complex as a constant strict tower.
Source: the constant-ring calculus (blueprint: def-sp-varying-ring-proper-open-arrows). -/
abbrev constantDerived (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    DerivedCategory (StrictTower.Modules B X) ⥤ StrictTower.Derived B X :=
  StrictTower.ConstantNormalization.delta B X

/-- Evaluation of this constant tower is canonically the original derived complex.
Source: Stacks 05RU (blueprint: def-sp-varying-ring-proper-open-arrows). -/
def constantEval (B : Type (u + 1)) [CommRing B] (X : Scheme.{u}) :
    constantDerived B X ⋙ StrictTower.ev B X 0 ≅
      𝟭 (DerivedCategory (StrictTower.Modules B X)) :=
  StrictTower.ConstantNormalization.deltaEval B X 0

end AlgebraicGeometry.ProEtale.VaryingRing
