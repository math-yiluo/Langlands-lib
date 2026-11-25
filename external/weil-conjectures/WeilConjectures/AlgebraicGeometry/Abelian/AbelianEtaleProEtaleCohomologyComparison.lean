/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections

import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Abelian etale–pro-etale cohomology comparison

Source: Stacks Project, proetale.tex, Tag 099W, part (1)
(blueprint: lem-cbc-abelian-etale-proetale-cohomology-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

/-- Full faithfulness on the bounded below derived categories gives bijectivity on Ext.
The single objects and their shifts lie in that full subcategory. Conjugate its Hom
bijection by the single-functor and shift isomorphisms; `mapExactFunctor_hom` identifies
this bijection with the specified Ext map. -/
private theorem mapExt_bijective_of_derivedPlus_fullyFaithful
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.mapDerivedCategoryPlus.Full] [L.mapDerivedCategoryPlus.Faithful]
    (X Y : C) (n : ℕ) : Function.Bijective (L.mapExtAddHom X Y n) := by
  let X' : DerivedCategory.Plus C :=
    ⟨(DerivedCategory.singleFunctor C 0).obj X, ⟨0, inferInstance⟩⟩
  let Y' : DerivedCategory.Plus C :=
    ⟨((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧,
      ⟨-(n : ℤ), DerivedCategory.TStructure.t.isGE_shift _ 0 (n : ℤ) (-(n : ℤ))⟩⟩
  let eC := (ObjectProperty.fullyFaithfulι DerivedCategory.TStructure.t.plus).homEquiv
    (X := X') (Y := Y')
  let eD := (ObjectProperty.fullyFaithfulι DerivedCategory.TStructure.t.plus).homEquiv
    (X := L.mapDerivedCategoryPlus.obj X') (Y := L.mapDerivedCategoryPlus.obj Y')
  have hb : Function.Bijective
      (L.mapDerivedCategory.map : (X'.obj ⟶ Y'.obj) → _) := by
    exact eD.bijective.comp
      (((Functor.FullyFaithful.ofFullyFaithful L.mapDerivedCategoryPlus).map_bijective
        X' Y').comp eC.symm.bijective)
  let eX := (L.mapDerivedCategorySingleFunctor 0).app X
  let eY := (L.mapDerivedCategory.commShiftIso (n : ℤ)).app
      ((DerivedCategory.singleFunctor C 0).obj Y) ≪≫
    (shiftFunctor (DerivedCategory D) (n : ℤ)).mapIso
      ((L.mapDerivedCategorySingleFunctor 0).app Y)
  let e := Abelian.Ext.homEquiv.trans
    ((Equiv.ofBijective _ hb).trans ((Iso.homCongr eX eY).trans
      Abelian.Ext.homEquiv.symm))
  convert e.bijective using 1
  ext x
  change (x.mapExactFunctor L).hom = Abelian.Ext.homEquiv
    (Abelian.Ext.homEquiv.symm (eX.inv ≫ L.mapDerivedCategory.map x.hom ≫ eY.hom))
  rw [Equiv.apply_symm_apply, Abelian.Ext.mapExactFunctor_hom]
  simp only [eX, eY, ShiftedHom.map, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_inv, Iso.app_hom, Category.assoc]

namespace AlgebraicGeometry.ProEtale

/-- Specialize the existing constant-sheaf pullback isomorphism and transport it to
the constructed comparison inverse image using the canonical adjunction isomorphism.
Source: Stacks Project, Tags 099R and 00YV
(blueprint: lem-cbc-abelian-etale-proetale-cohomology-comparison). -/
noncomputable def comparisonConstantSheafIso (T : Scheme.{u}) :
    constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      comparisonUpperStar AddCommGrpCat.{u + 1} T ≅
        constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Scheme.toProEt T)
      AddCommGrpCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).symm ≪≫
    (Scheme.toProEt T).constantSheafsheafPullbackIso AddCommGrpCat.{u + 1}
      T.smallEtaleTopology (Scheme.ProEt.topology T)
      (terminalIsTerminal : IsTerminal (⊤_ T.Etale))
      (terminalIsTerminal.isTerminalObj (Scheme.toProEt T))

/-- The canonical cohomology pullback: apply exact comparison inverse image to an
Ext class and precompose with the canonical constant-sheaf comparison.
Source: Stacks Project, Tag 099W and Cohomology on Sites, Remark 08J6
(blueprint: lem-cbc-abelian-etale-proetale-cohomology-comparison). -/
noncomputable def comparisonCohomologyMap (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Sheaf.H F i →+
      Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj F) i :=
  Sheaf.H.mapFunctor (comparisonUpperStar AddCommGrpCat.{u + 1} T)
    ((comparisonConstantSheafIso T).symm.app (AddCommGrpCat.of (ULift ℤ))) F i

/-- For every abelian etale sheaf, canonical pullback is an isomorphism in every
nonnegative degree, without coefficient restrictions.
Source: Stacks Project, Tag 099W, part (1)
(blueprint: lem-cbc-abelian-etale-proetale-cohomology-comparison).

Proof: the comparison unit is an isomorphism on sections over every etale object
by lem-cbc-comparison-pullback-sections, hence naturally an isomorphism of abelian
sheaves. Pull an injective resolution of F back by the exact inverse image.
Its terms are comparison-direct-image acyclic by
lem-cbc-abelian-comparison-injective-acyclicity. The acyclic-resolution criterion
lemma-weil-pbc-leray-acyclicity computes the higher direct images by the original
resolution, using the unit, so they vanish in positive degrees. The Leray edge
isomorphism of lem-weil-pbc-site-leray-degenerate, composed with cohomology of the
unit, is an isomorphism. Naturality of cohomology pullback and the adjunction
triangle identity identify this composite with comparisonCohomologyMap. In degree
zero this is the unit on global sections. -/
theorem comparisonCohomologyMap_bijective (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Function.Bijective (comparisonCohomologyMap T F i) := by
  let L := comparisonUpperStar AddCommGrpCat.{u + 1} T
  let adj := comparisonAdjunction AddCommGrpCat.{u + 1} T
  have hu := isIso_comparisonAdjunction_unit AddCommGrpCat.{u + 1} T
  have (X : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
      IsIso (adj.derivedPlus.unit.app X) :=
    adj.isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun _ _ ↦ inferInstance)
      (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective
        AddCommGrpCat.{u + 1} T I) X
  have : IsIso adj.derivedPlus.unit := NatIso.isIso_of_isIso_app _
  let ff := adj.derivedPlus.fullyFaithfulLOfIsIsoUnit
  let : L.mapDerivedCategoryPlus.Full := ff.full
  let : L.mapDerivedCategoryPlus.Faithful := ff.faithful
  exact (Abelian.Ext.precompAddEquiv
    ((comparisonConstantSheafIso T).symm.app (AddCommGrpCat.of (ULift ℤ))) _ i).bijective.comp
      (mapExt_bijective_of_derivedPlus_fullyFaithful L _ F i)

end AlgebraicGeometry.ProEtale
