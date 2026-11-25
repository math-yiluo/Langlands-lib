/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.AlgebraicGeometry.FreeRepresentableHomotopyHomology
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-! # Object cohomology as homology of the presheaf resolution

Source: Stacks Project, Cohomology on Sites, Section 01FT and Tag 03F3.
(blueprint: lem-weil-pbc-object-cohomology-presheaf-resolution)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

private noncomputable def resolutionHomotopyEquiv
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {F X : A} (I : InjectiveResolution F) (q : ℕ) :
    Abelian.Ext X F q ≃+
      ((HomotopyCategory.quotient A (.up ℤ)).obj ((CochainComplex.singleFunctor A 0).obj X) ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj (I.cochainComplex⟦(q : ℤ)⟧)) :=
  (I.extAddEquivCohomologyClass (X := X) (n := q)).trans
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv

private theorem resolutionHomotopyEquiv_naturality
    {A : Type*} [Category* A] [Abelian A] [HasExt.{w} A]
    {F X Y : A} (I : InjectiveResolution F) (q : ℕ) (g : Y ⟶ X)
    (a : Abelian.Ext X F q) :
    resolutionHomotopyEquiv I q ((Abelian.Ext.mk₀ g).comp a (zero_add q)) =
      (HomotopyCategory.quotient _ (.up ℤ)).map ((CochainComplex.singleFunctor A 0).map g) ≫
        resolutionHomotopyEquiv I q a := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨f, hf, rfl⟩ := I.extMk_surjective a (q + 1) rfl
    rw [I.mk₀_comp_extMk]
    simp only [resolutionHomotopyEquiv, AddEquiv.trans_apply,
      InjectiveResolution.extAddEquivCohomologyClass_apply,
      I.extEquivCohomologyClass_extMk, CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply,
      CochainComplex.HomComplex.CohomologyClass.toHom_mk]
    simp only [Category.assoc]
    rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_precomp,
      CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

/-- Object cohomology is naturally the objectwise homology of any injective resolution.
Source: Stacks Project, Section 01FT, definition of cohomology over an object;
Tag 03F3, proof. The Ext formulation uses the free abelian representable adjunction.
(blueprint: lem-weil-pbc-object-cohomology-presheaf-resolution)

Proof: For U in C, let A(U) be the sheafification of the free abelian presheaf
on yoneda(U). Sheafification, the free abelian adjunction and Yoneda give the
additive identification Hom(A(U),G) = G(U), natural in both U and G. Applied
degreewise to I, it identifies the Hom complex from A(U) with I evaluated at U.
Since I is an injective resolution, Ext(A(U),F,q) is the degree-q homology of
this complex. One can use the extended integer complex and then its nonnegative
restriction; q is nonnegative, and the negative terms are zero, including the
incoming differential for q=0. The identification is natural for morphisms U -> V:
precomposition with A(U) -> A(V) corresponds to the restriction G(V) -> G(U)
in every degree. Taking homology preserves this equality. The objectwise homology
in the presheaf category evaluates to these groups by exactness of evaluation.
Compute Ext using I in the sheaf morphism universe, compare the given HasExt
universe by the canonical universe-independent Ext equivalence, and lift both
group-valued presheaves to max(u,v,w). These component isomorphisms and the
restriction compatibility assemble into the displayed natural isomorphism.
No enough-injectives assumption is required since I is supplied. The assertion
includes the empty site, zero sheaf and degree zero. -/
theorem objectCohomologyPresheaf_resolution
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (I : InjectiveResolution F) (q : ℕ) :
    Nonempty
      (Sheaf.cohomologyPresheaf F q ⋙ AddCommGrpCat.uliftFunctor.{max u v, w} ≅
        (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex).homology q ⋙ AddCommGrpCat.uliftFunctor.{max u w, v}) := by
  set_option backward.isDefEq.respectTransparency false in
    let e : Sheaf.cohomologyPresheaf F q ⋙ AddCommGrpCat.uliftFunctor.{max u v, w} ≅
        freeRepresentableHomotopyPresheaf J I.cocomplex q ⋙
          AddCommGrpCat.uliftFunctor.{w, max u v} :=
      NatIso.ofComponents (fun X ↦
        ((AddEquiv.ulift.trans (resolutionHomotopyEquiv I q)).trans
          AddEquiv.ulift.symm).toAddCommGrpIso) (by
        intro X Y f
        ext a
        exact congrArg ULift.up (resolutionHomotopyEquiv_naturality I q
          ((presheafToSheaf J AddCommGrpCat.{v}).map
            (Functor.whiskerRight (yoneda.map f.unop) AddCommGrpCat.free)) a.down))
    obtain ⟨h⟩ := freeRepresentableHomotopyPresheaf_homology J I.cocomplex q
    exact ⟨e ≪≫ h⟩
