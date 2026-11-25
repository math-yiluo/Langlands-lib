/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private lemma homObj_epi_ext (X : Scheme.{u}) (U : X.Opens)
    {M M' N : X.Modules} (q : M' ⟶ M) [Epi q]
    (f g : (SheafOfModules.homObj (R := X.sheaf) M N).val.obj (op U))
    (h : (PresheafOfModules.restrictOver X.sheaf.obj U).map q.val ≫ f =
      (PresheafOfModules.restrictOver X.sheaf.obj U).map q.val ≫ g) : f = g := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  have : PreservesFiniteColimits F := by
    dsimp [F, SheafOfModules.overFunctor]
    infer_instance
  have : Epi (F.map q) := inferInstance
  let hf : (F.obj M ⟶ F.obj N) := ⟨f⟩
  let hg : (F.obj M ⟶ F.obj N) := ⟨g⟩
  have he : F.map q ≫ hf = F.map q ≫ hg := by
    apply SheafOfModules.hom_ext
    dsimp [hf, hg, F, SheafOfModules.overFunctor, SheafOfModules.pushforward]
    exact h
  have he' := congrArg SheafOfModules.Hom.val ((cancel_epi (F.map q)).mp he)
  exact he'

private lemma homObj_comp_naturality_apply (X : Scheme.{u})
    {A B M N : X.Modules} (q : A ⟶ B)
    (a : B ⟶ SheafOfModules.homObj (R := X.sheaf) M N)
    (U : X.Opensᵒᵖ) (φ : A.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (z : M.val.obj (op W.unop.left)) :
    (a.val.app (op W.unop.left)
      (q.val.app (op W.unop.left) (A.val.map W.unop.hom.op φ))).app
        (op (Over.mk (𝟙 W.unop.left))) z =
      (a.val.app U (q.val.app U φ)).app W z := by
  rw [PresheafOfModules.naturality_apply q.val W.unop.hom.op]
  rw [PresheafOfModules.naturality_apply a.val W.unop.hom.op]
  exact PresheafOfModules.restrictOver_hom_app_congr _ (Category.id_comp W.unop.hom) _

set_option backward.isDefEq.respectTransparency false in
-- Restricting sections unfolds the localized internal-Hom module structures.
/-- Cycle formulas determine a morphism once every local cycle has a target-cycle lift.
Source: Stacks Project, Tag 08DH, separatedness of internal Hom.
(blueprint: new-b2-homology-evaluation-uniqueness-ext).

Cancel the epimorphism from Hom cycles to Hom homology. For a fixed cycle section
on U, its two images are morphisms of module sheaves on the site over U. Restriction
to that site preserves finite colimits, hence preserves the epimorphism from T-cycles
to T-homology. Cancel this second epimorphism. At an arbitrary slice object V -> U,
restrict the Hom cycle to V and use the assumed lift b. Both cycle formulas identify
the evaluations with the same class of b. Naturality of the homology class map and
of e and e' identifies these evaluations with their components on the slice object.
Extensionality now concludes equality. No pointwise surjectivity is assumed; this
also covers empty opens and zero homology sheaves.
-/
theorem homologyEvaluation_unique_of_cycle_of_local_lifts
    (X : AlgebraicGeometry.Scheme.{u}) (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e e' : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e)
    (he' : IsHomologyEvaluation X T J n e')
    (hlift : ∀ (U : X.Opens)
      (φ : ((homComplex (R := X.sheaf) T J).cycles n).val.obj (op U))
      (z : (T.cycles (-n)).val.obj (op U)),
      ∃ b : (J.cycles 0).val.obj (op U),
        (J.iCycles 0).val.app (op U) b =
          ((homologyEvaluationProjection X T J n).val.app (op U)
            (((homComplex (R := X.sheaf) T J).iCycles n).val.app (op U) φ)).app
              (op (Over.mk (𝟙 U)))
            (((T.iCycles (-n)).val.app (op U)) z)) :
    e = e' := by
  let P := homComplex (R := X.sheaf) T J
  apply (cancel_epi (P.homologyπ n)).mp
  apply SheafOfModules.hom_ext
  ext U φ : 3
  apply homObj_epi_ext X U.unop (T.homologyπ (-n))
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let V := W.unop.left
  let φV := (P.cycles n).val.map W.unop.hom.op φ
  obtain ⟨b, hb⟩ := hlift V φV z
  have hv := (he V φV z b hb).trans (he' V φV z b hb).symm
  exact (homObj_comp_naturality_apply X (P.homologyπ n) e U φ W
    ((T.homologyπ (-n)).val.app (op V) z)).symm.trans
      (hv.trans (homObj_comp_naturality_apply X (P.homologyπ n) e' U φ W
        ((T.homologyπ (-n)).val.app (op V) z)))

end CategoryTheory
