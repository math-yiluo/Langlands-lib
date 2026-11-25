/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexCoefficients
public import WeilConjectures.CategoryTheory.Sites.CechComplexRelativeLimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Čech complexes with coefficients along a cofiltered limit of morphisms

Let `F : C' ⥤ C` be a functor and `q : W ⟶ V` a morphism of `C` which is a cofiltered limit
`q = limⱼ F(αⱼ)` of morphisms `αⱼ : Wⱼ ⟶ Vⱼ` of `C'`, presented by relative limit presentations
indexed by `J`. Let `P` be a presheaf on `C` with values in an abelian category `A` in which
colimits of shape `Jᵒᵖ` exist and are exact, and which sends such cofiltered limits to colimits.
Degreewise, the Čech complex `Č(q, P)` is then the colimit of the Čech complexes
`Č(αⱼ, F.op ⋙ P)` (by `CategoryTheory.Presheaf.isLimitStageNerveCone`), so exactness in positive
degrees passes from the stages to the limit.

This is the analogue of `CategoryTheory.Presheaf.exactAt_cechComplex_of_relativeLimitPresentation`
for an arbitrary abelian coefficient category, with an element-free proof.

## Main statements

- `CategoryTheory.Presheaf.exactAt_overCechComplex_of_relativeLimitPresentation`: exactness of
  Čech complexes passes to the limit.
-/

@[expose] public section

universe t w v v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Presheaf

section Exactness

variable {C' : Type w} [Category.{v} C'] {C : Type w} [Category.{v} C] {F : C' ⥤ C}
  {J : Type t} [SmallCategory J] {V W : C}
  {pV : RelativeLimitPresentation J F V} {pW : RelativeLimitPresentation J F W}
  (h : pW.Hom pV) [∀ j, HasFiniteProducts (Over (pV.diag.obj j))] [HasFiniteProducts (Over V)]
  [∀ j, PreservesFiniteProducts (Over.post F (X := pV.diag.obj j))]
  {A : Type u'} [Category.{v'} A] [Abelian A] (P : Cᵒᵖ ⥤ A)

/-- The diagram `j ↦ P(F(Wⱼ ×_{Vⱼ} ⋯ ×_{Vⱼ} Wⱼ))` (`k + 1` factors) of the degree `k` terms of
the Čech complexes of `F.op ⋙ P` for the stages. -/
noncomputable abbrev stageCechDiagram (k : ℕ) : Jᵒᵖ ⥤ A :=
  (stageNerve h (fun _ : Fin (k + 1) ↦ 0) ⋙ F).op ⋙ P

omit [HasFiniteProducts (Over V)]
  [∀ j, PreservesFiniteProducts (Over.post F (X := pV.diag.obj j))] in
/-- The Čech differentials of the stages commute with the transition maps: for `g : i ⟶ j` the
square
```
Čᵏ(αⱼ, F.op ⋙ P) ──d──▶ Čᵏ⁺¹(αⱼ, F.op ⋙ P)
       │g^*                       │g^*
       ▼                          ▼
Čᵏ(αᵢ, F.op ⋙ P) ──d──▶ Čᵏ⁺¹(αᵢ, F.op ⋙ P)
```
commutes. -/
lemma stageTransition_overCechComplex_d {i j : J} (g : i ⟶ j) (k : ℕ) :
    P.map (F.map (stageNerveMap h g (fun _ : Fin (k + 1) ↦ 0))).op ≫
        ((overCechComplex (Over.mk (h.natTrans.app i))).obj (F.op ⋙ P)).d k (k + 1) =
      ((overCechComplex (Over.mk (h.natTrans.app j))).obj (F.op ⋙ P)).d k (k + 1) ≫
        P.map (F.map (stageNerveMap h g (fun _ : Fin (k + 2) ↦ 0))).op := by
  rw [overCechComplex_obj_d, overCechComplex_obj_d, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Functor.comp_map, Functor.comp_map,
    ← P.map_comp, ← P.map_comp, Functor.op_map, Functor.op_map, ← op_comp, ← op_comp,
    Quiver.Hom.unop_op, Quiver.Hom.unop_op, ← F.map_comp, ← F.map_comp]
  exact congrArg (fun x ↦ (-1 : ℤ) ^ (l : ℕ) • P.map (F.map x).op)
    (stageNerveMap_cechNerveMap h g (fun _ : Fin (k + 2) ↦ 0) l.succAbove).symm

/-- The Čech differentials of the stages, as a natural transformation. -/
noncomputable def stageCechDiagramD (k : ℕ) :
    stageCechDiagram h P k ⟶ stageCechDiagram h P (k + 1) where
  app j := ((overCechComplex (Over.mk (h.natTrans.app j.unop))).obj (F.op ⋙ P)).d k (k + 1)
  naturality _ _ g := stageTransition_overCechComplex_d h P g.unop k

/-- The Čech differential of the limit commutes with the projections to the stages: the square
```
Čᵏ(αⱼ, F.op ⋙ P) ──d──▶ Čᵏ⁺¹(αⱼ, F.op ⋙ P)
       │                          │
       ▼                          ▼
   Čᵏ(q, P)      ──d──▶    Čᵏ⁺¹(q, P)
```
whose vertical maps are induced by the projections of the limit to the stage `j` commutes. -/
lemma overCechComplex_d_limitNerveLeg (j : J) (k : ℕ) :
    ((overCechComplex (Over.mk (h.natTrans.app j))).obj (F.op ⋙ P)).d k (k + 1) ≫
        P.map (limitNerveLeg h j (fun _ : Fin (k + 2) ↦ 0)).op =
      P.map (limitNerveLeg h j (fun _ : Fin (k + 1) ↦ 0)).op ≫
        ((overCechComplex (Over.mk h.map)).obj P).d k (k + 1) := by
  rw [overCechComplex_obj_d, overCechComplex_obj_d, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Functor.comp_map, ← P.map_comp,
    ← P.map_comp, Functor.op_map, ← op_comp, ← op_comp, Quiver.Hom.unop_op]
  exact congrArg (fun x ↦ (-1 : ℤ) ^ (l : ℕ) • P.map x.op)
    (limitNerveLeg_cechNerveMap h j (fun _ : Fin (k + 2) ↦ 0) l.succAbove)

variable [IsCofiltered J] [HasColimitsOfShape Jᵒᵖ A] [HasExactColimitsOfShape Jᵒᵖ A]

/-- **Čech complexes along a cofiltered limit of morphisms, with coefficients in an abelian
category.** Let `q : W ⟶ V` be the cofiltered limit of morphisms `αⱼ : Wⱼ ⟶ Vⱼ` of `C'` under
`F : C' ⥤ C`, and let `P` be a presheaf on `C` with values in an abelian category with exact
colimits of shape `Jᵒᵖ`, sending such cofiltered limits to filtered colimits. If the Čech
complexes of `F.op ⋙ P` for all the `αⱼ` are exact in positive degrees, so is the Čech complex
of `P` for `q`: it is the filtered colimit of the former. -/
theorem exactAt_overCechComplex_of_relativeLimitPresentation
    [F.PreservesRelativeFilteredColimits.{t} P]
    (hstage : ∀ (j : J) (q : ℕ),
      ((overCechComplex (Over.mk (h.natTrans.app j))).obj (F.op ⋙ P)).ExactAt (q + 1))
    (q : ℕ) : ((overCechComplex (Over.mk h.map)).obj P).ExactAt (q + 1) := by
  have hcol (k : ℕ) :=
    (Functor.PreservesRelativeFilteredColimits.nonempty_isColimit (F := F) (P := P)
      (stageNerveCone h (fun _ : Fin (k + 1) ↦ 0)) (isLimitStageNerveCone h _)).some
  let S : ShortComplex (Jᵒᵖ ⥤ A) :=
    ShortComplex.mk (stageCechDiagramD h P q) (stageCechDiagramD h P (q + 1)) (by
      ext j
      exact ((overCechComplex (Over.mk (h.natTrans.app j.unop))).obj (F.op ⋙ P)).d_comp_d _ _ _)
  have hS : S.Exact := (ShortComplex.exact_iff_evaluation S).2 fun j ↦ by
    have := hstage j.unop q
    rwa [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)] at this
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)]
  exact colim.exact_mapShortComplex hS (hcol q) (hcol (q + 1)) (hcol (q + 2)) _ _
    (fun j ↦ (overCechComplex_d_limitNerveLeg h P j.unop q).symm)
    (fun j ↦ (overCechComplex_d_limitNerveLeg h P j.unop (q + 1)).symm)

end Exactness

end Presheaf

end CategoryTheory
