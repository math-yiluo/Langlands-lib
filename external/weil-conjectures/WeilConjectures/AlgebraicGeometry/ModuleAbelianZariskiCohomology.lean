/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Cohomology of a module sheaf agrees with that of its underlying abelian sheaf

Source: Stacks Project, sites-cohomology.tex, Lemma Tag 03FD
(blueprint: lem-sc-module-abelian-zariski-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- The free abelian sheaf on the terminal open is the constant integer sheaf,
so precomposition identifies the two Ext definitions of global cohomology. -/
private noncomputable def topCohomologyEquiv (X : TopCat.{u})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    Sheaf.H' F q ⊤ ≃+ Sheaf.H.{u} F q := by
  let e : yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free ≅
      (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦ by
      letI : Unique (U.unop ⟶ (⊤ : Opens X)) :=
        ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
      exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro a
        simp [FreeAbelianGroup.uniqueEquiv])
  let eS := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
  exact (Abelian.Ext.precompAddEquiv eS F q).symm

/-- Combine the terminal-open Ext identification with derived evaluation.
Degree zero uses the constant-sheaf adjunction; positive degrees use the existing
injective-resolution comparison. -/
private theorem topCohomologyIsoDerived (X : TopCat.{u})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    Nonempty (Sheaf.H' F q ⊤ ≅
      (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op ⊤)).rightDerived q).obj
        F)) := by
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op ⊤)
  have hT : IsTerminal (⊤ : Opens X) := Limits.isTerminalTop
  have h : Nonempty (Sheaf.H.{u} F q ≃+ (Γ.rightDerived q).obj F) := by
    cases q with
    | zero =>
      exact ⟨(Sheaf.H.equiv₀ F hT).trans
        ((Γ.rightDerivedZeroIsoSelf.app F).addCommGroupIsoToAddEquiv.symm)⟩
    | succ n =>
      exact Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
        (Opens.grothendieckTopology X) ⊤ hT F n
  obtain ⟨e⟩ := h
  exact ⟨((topCohomologyEquiv X F q).trans e).toAddCommGrpIso⟩

/-- The right-derived cohomology of an `O_X`-module sheaf agrees with the
cohomology of its underlying abelian sheaf, naturally in the module sheaf.
Source: Stacks Project, sites-cohomology.tex, Lemma Tag 03FD.
Proof: forgetful exactness and an injective module resolution give an injective
resolution after forgetting; the acyclic-resolution comparison identifies both
cohomologies, naturally in the sheaf (blueprint: lem-sc-module-abelian-zariski-cohomology). -/
theorem module_cohomology_iso_underlying_abelian
    (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (q : ℕ)
    [hE : EnoughInjectives (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] :
    Nonempty
      ((forget₂ (ModuleCat.{u}
          ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat).obj
          ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≅
        @CategoryTheory.Sheaf.H' _ _ _ _
          (CategoryTheory.hasExt_of_enoughInjectives _)
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)
          q ⊤) := by
  let : HasExt.{u}
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    CategoryTheory.hasExt_of_enoughInjectives _
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤))) AddCommGrpCat
  have : PreservesFiniteLimits T := inferInstance
  have : PreservesFiniteColimits T := inferInstance
  have : T.PreservesHomology := inferInstance
  have hac : ∀ I, Injective I → Γ.rightAcyclic (T.obj I) := by
    intro I hI n
    let : Injective I := hI
    let : Subsingleton (Sheaf.H' (T.obj I) (n + 1) ⊤) :=
      injective_module_abelian_acyclic ⊤ I (n + 1) (Nat.succ_pos n)
    obtain ⟨e⟩ := topCohomologyIsoDerived X.carrier (T.obj I) (n + 1)
    exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso e.symm
  obtain ⟨d⟩ := topCohomologyIsoDerived X.carrier (T.obj F) q
  -- Forgetting an injective resolution gives an exact, termwise Γ-acyclic resolution.
  let I := injectiveResolution F
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let e := I.isoRightDerivedObj G q
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) :=
    inferInstance
  have : QuasiIso ι := quasiIso_comp _ _
  let c := Γ.rightDerivedObjIsoOfResolution ι (fun n ↦ hac (I.cocomplex.X n)
    inferInstance) q
  -- Module and abelian evaluation have the same underlying section complex.
  have hcomp : G ⋙ V ≅ T ⋙ Γ := Iso.refl _
  let eK := (Functor.mapHomologicalComplexCompIso hcomp (ComplexShape.up ℕ)).app
    I.cocomplex
  let eL := (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ Γ))
    (ComplexShape.up ℕ)).app I.cocomplex
  exact ⟨V.mapIso e ≪≫ ((K.sc q).mapHomologyIso V).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso (eK ≪≫ eL.symm) ≪≫
    c.symm ≪≫ d.symm⟩

end AlgebraicGeometry
