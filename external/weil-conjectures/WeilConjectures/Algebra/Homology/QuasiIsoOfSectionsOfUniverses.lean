/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Detecting quasi-isomorphisms through sections

Source: Stacks Project, sites-cohomology.tex, proof of Lemma 0A95
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Sectionwise quasi-isomorphisms induce quasi-isomorphisms of module sheaves.
Source: Stacks Project, sites-cohomology.tex, proof of Lemma 0A95
(auxiliary; not a blueprint node).

Proof: forget the module structure and view the complexes as complexes of presheaves of
abelian groups. Evaluation at each site object is exact and jointly detects their cohomology
isomorphisms. Sheafification is exact, so the presheaf quasi-isomorphism remains one after
sheafification. The counit of sheafification identifies the resulting complexes naturally
with the original abelian-sheaf complexes. Finally the exact forgetful functor from module
sheaves to abelian sheaves reflects isomorphisms, hence reflects quasi-isomorphisms. -/
theorem quasiIso_of_sectionsOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J RingCat.{max u v r}}
    {K L : CochainComplex (SheafOfModules.{max u v r} R) ℤ} (f : K ⟶ L)
    (h : ∀ U : C, QuasiIso (((SheafOfModules.forget R ⋙
      PresheafOfModules.evaluation R.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let T := SheafOfModules.toSheaf R
  let V := sheafToPresheaf J AddCommGrpCat.{max u v r}
  let A := presheafToSheaf J AddCommGrpCat.{max u v r}
  let g := ((T ⋙ V).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  have hg : QuasiIso g := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro U
    let ec := Functor.mapHomologicalComplexCompIso
      (F := T ⋙ V) (G := (evaluation Cᵒᵖ AddCommGrpCat.{max u v r}).obj U)
      (H := SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj U ⋙
        forget₂ (ModuleCat.{max u v r} (R.obj.obj U)) AddCommGrpCat)
      (Iso.refl _) (ComplexShape.up ℤ)
    have hh := h U.unop
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso ec.symm (Arrow.mk f))).mp hh
  have hg' : QuasiIso ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
    infer_instance
  let e : (T ⋙ V) ⋙ A ≅ T :=
    Functor.associator T V A ≪≫
    Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction J
      AddCommGrpCat.{max u v r}).counit) ≪≫ T.rightUnitor
  let ec := Functor.mapHomologicalComplexCompIso
    (F := T ⋙ V) (G := A) (Iso.refl ((T ⋙ V) ⋙ A)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
  have ht : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso ec (Arrow.mk f))).mp hg'
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f T).mp ht

end CategoryTheory
