/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Sections of an injective resolution compute object cohomology

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 3; Mathlib's computation of
Ext.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Sheaf

open Limits Opposite CochainComplex HomComplex

private noncomputable abbrev freeSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C) :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj X ⋙ AddCommGrpCat.free)

private noncomputable def sectionEquiv
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J X ⟶ F) ≃+ F.obj.obj (op X) := by
  let e := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj X) F.obj).trans
      yonedaEquiv)
  refine { toEquiv := e, map_add' := ?_ }
  intro a b
  dsimp [e, Adjunction.homEquiv, yonedaEquiv]

private lemma sectionEquiv_naturality
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C)
    {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (a : freeSheaf J X ⟶ F) :
    sectionEquiv J X G (a ≫ f) = f.hom.app (op X) (sectionEquiv J X F a) := by
  change yonedaEquiv
    (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj X) G.obj)
      (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ G) (a ≫ f))) =
    f.hom.app (op X) (yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (C := Cᵒᵖ)).homEquiv (yoneda.obj X) F.obj)
        (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F) a)))
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionComplexIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj (freeSheaf J X)) K ≅
      (((sheafToPresheaf J AddCommGrpCat.{v} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X) ⋙
          AddCommGrpCat.uliftFunctor.{u, v}).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      ((sectionEquiv J X (K.X n)).trans AddEquiv.ulift.symm)).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
        change ULift.up ((K.d i j).hom.app (op X)
          (sectionEquiv J X (K.X i)
            (Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk a (zero_add i))))) =
          ULift.up (sectionEquiv J X (K.X j)
            (Cochain.fromSingleEquiv (zero_add j)
              (δ i j (Cochain.fromSingleMk a (zero_add i)))))
        simp only [Cochain.δ_fromSingleMk, zero_add, Cochain.fromSingleEquiv_fromSingleMk]
        exact congrArg ULift.up (sectionEquiv_naturality J X (K.d i j) a).symm)

/-- The section complex of any specified injective resolution computes object cohomology.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 3; the free-abelian
sheafification adjunction and Mathlib's injective-resolution computation of Ext.
(blueprint: lem-sc-resolution-section-cohomology)

Proof: Sheafification adjunction identifies morphisms from the free abelian sheaf on X
with morphisms from the free abelian representable presheaf. The free-forgetful
adjunction and Yoneda identify these naturally and additively with sections at X.
In every degree of the integer extension of I, this gives an isomorphism from the
Hom complex out of the single free sheaf to the lifted section complex. Naturality
in the resolution differential proves compatibility with the differentials.
Mathlib identifies Ext with cohomology classes of this Hom complex. Its homology
is those cohomology classes. Transport along the complex isomorphism and use
preservation of homology by the universe-lift functor, then unlift the groups.
This applies also in degree zero and requires no terminal-object hypothesis. -/
theorem resolution_section_cohomology
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (X : C) (n : ℕ) :
    Nonempty ((((sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
        (.up ℤ)).obj I.cochainComplex).homology (n : ℤ) ≅ F.H' n X) := by
  let E := sheafToPresheaf J AddCommGrpCat.{v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X)
  let e := (CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor _ 0).obj (freeSheaf J X))
    I.cochainComplex (n : ℤ)).homologyIso.symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
        (sectionComplexIso J X I.cochainComplex) ≪≫
      (((E.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc
        (n : ℤ)).mapHomologyIso AddCommGrpCat.uliftFunctor.{u, v}
  exact ⟨((I.extAddEquivCohomologyClass.trans
    ((e.addCommGroupIsoToAddEquiv).trans AddEquiv.ulift)).symm).toAddCommGrpIso⟩

end CategoryTheory.Sheaf
