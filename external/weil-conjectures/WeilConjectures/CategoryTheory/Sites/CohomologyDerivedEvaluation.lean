/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Ext sheaf cohomology and right-derived evaluation

Source: Stacks Project, Cohomology on Sites, Section 21.2 (Definition of cohomology).
(blueprint: new-sheaf-cohomology-derived-evaluation)
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.Sheaf

open CochainComplex HomComplex Limits Opposite in
private noncomputable abbrev integerSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

open CochainComplex HomComplex Limits Opposite in
private noncomputable def evaluationEquiv
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] (T : C) (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{w}) :
    (integerSheaf J ⟶ F) ≃+ F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat hT).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

open CochainComplex HomComplex Limits Opposite in
private lemma evaluationEquiv_naturality
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] (T : C) (hT : IsTerminal T)
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (a : integerSheaf J ⟶ F) :
    evaluationEquiv J T hT G (a ≫ f) =
      f.hom.app (op T) (evaluationEquiv J T hT F a) := by
  dsimp only [evaluationEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Opposite in
private noncomputable def complexEvaluationIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] (T : C) (hT : IsTerminal T)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :
    HomComplex ((CochainComplex.singleFunctor _ 0).obj (integerSheaf J)) K ≅
      (((sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T) ⋙
          AddCommGrpCat.uliftFunctor.{u, w}).mapHomologicalComplex
          (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ ((Cochain.fromSingleEquiv (zero_add n)).trans
      ((evaluationEquiv J T hT (K.X n)).trans AddEquiv.ulift.symm)).toAddCommGrpIso) (by
        intro i j hij
        ext a
        obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a i (zero_add i)
        change ULift.up ((K.d i j).hom.app (op T)
          (evaluationEquiv J T hT (K.X i)
            (Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk a (zero_add i))))) =
          ULift.up (evaluationEquiv J T hT (K.X j)
            (Cochain.fromSingleEquiv (zero_add j)
              (δ i j (Cochain.fromSingleMk a (zero_add i)))))
        simp only [Cochain.δ_fromSingleMk, zero_add, Cochain.fromSingleEquiv_fromSingleMk]
        exact congrArg ULift.up (evaluationEquiv_naturality J T hT (K.d i j) a).symm)

/-- Ext from the constant integer sheaf computes right-derived evaluation at a
terminal object of the site, in positive degrees.
Source: Stacks Project, Cohomology on Sites, Section 21.2, definition of cohomology;
Mathlib's definition of Sheaf.H and computation of Ext by an injective resolution.
(blueprint: new-sheaf-cohomology-derived-evaluation)

Proof: Let Z be the constant sheaf associated to the lifted integers. The
constant-sheaf adjunction at the terminal object T, followed by evaluation at 1,
identifies Hom(Z,F) additively and naturally with F(T). Choose an injective
resolution of F. The same natural identification in every degree identifies its
Hom(Z,-) complex with its evaluation complex and commutes with differentials.
The cohomology of the first complex in degree q+1 is Ext^(q+1)(Z,F), by the
injective-resolution computation of Ext, hence is Sheaf.H F (q+1). The cohomology
of the second is the (q+1)-st right-derived evaluation of F, by the
injective-resolution computation of right-derived functors. Compose these additive
identifications. No injectivity
assumption on F is needed: its resolution is taken in the category of abelian sheaves. -/
theorem cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{w})]
    (T : C) (hT : Limits.IsTerminal T) (F : Sheaf J AddCommGrpCat.{w}) (q : ℕ) :
    Nonempty
      (Sheaf.H F (q + 1) ≃+
        (((sheafToPresheaf J AddCommGrpCat.{w} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op T)).rightDerived
            (q + 1)).obj F)) := by
  let R := injectiveResolution F
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op T)
  -- The Hom complex uses a larger universe than the values of E. Lift those
  -- values, compute homology there, and use preservation of homology to unlift.
  let e := (CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor _ 0).obj (integerSheaf J))
    R.cochainComplex (q + 1 : ℕ)).homologyIso.symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ ((q + 1 : ℕ) : ℤ)).mapIso
        (complexEvaluationIso J T hT R.cochainComplex) ≪≫
      (((E.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).sc
        ((q + 1 : ℕ) : ℤ)).mapHomologyIso AddCommGrpCat.uliftFunctor.{u, w} ≪≫
      AddCommGrpCat.uliftFunctor.{u, w}.mapIso
        (R.isoRightDerivedObjCochainComplex E (q + 1)).symm
  exact ⟨R.extAddEquivCohomologyClass.trans
    ((e.addCommGroupIsoToAddEquiv).trans AddEquiv.ulift)⟩

end CategoryTheory.Sheaf
