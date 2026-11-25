/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor

/-!
# Čech complexes of families with a section

If one member of a family `U : ι → C` receives a morphism from the terminal object, the
Čech complex `cechComplexFunctor U` of every presheaf is exact in positive degrees: the
Čech object then has an extra degeneracy.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A] {ι : Type w}

/-- If some member of the family `U` receives a morphism from the terminal object, then the
Čech complex of any presheaf with respect to `U` is exact in positive degrees.

Proof: the augmented Čech object has an extra degeneracy
(`FormalCoproduct.extraDegeneracyCech`). Evaluating the presheaf turns it into an augmented
simplicial object of `Aᵒᵖ` with an extra degeneracy, whose alternating face map complex is
homotopy equivalent to a complex concentrated in degree zero. Its unopposite is the Čech
complex. -/
theorem cechComplexFunctor_exactAt_succ_of_hom (U : ι → C) {T : C} (hT : IsTerminal T)
    {i₀ : ι} (s : T ⟶ U i₀) (P : Cᵒᵖ ⥤ A) (q : ℕ) :
    ((cechComplexFunctor U).obj P).ExactAt (q + 1) := by
  let X := (FormalCoproduct.mk _ U).cech.augmentOfIsTerminal
    (FormalCoproduct.isTerminalIncl _ hT)
  let ed : X.ExtraDegeneracy := (FormalCoproduct.mk _ U).extraDegeneracyCech hT (i₀ := i₀) s
  let G : FormalCoproduct.{w} C ⥤ Aᵒᵖ := ((FormalCoproduct.evalOp.{w} C A).obj P).rightOp
  let e := (ed.map G).homotopyEquiv
  have h : (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj
        (((SimplicialObject.Augmented.whiskering _ _).obj G).obj X))).ExactAt (q + 1) := by
    rw [exactAt_iff_of_quasiIsoAt e.hom]
    exact HomologicalComplex.exactAt_single_obj _ _ _ _ (by simp)
  have hd (m : ℕ) : ((cechComplexFunctor U).obj P).d m (m + 1) =
      ((AlgebraicTopology.AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj
          (((SimplicialObject.Augmented.whiskering _ _).obj G).obj X))).d (m + 1) m).unop := by
    rw [cechComplexFunctor_obj_d, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
      unop_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [unop_zsmul]
    rfl
  have h' := h.unop
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)]
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (ComplexShape.prev_eq' _ rfl)
    (ComplexShape.next_eq' _ rfl)] at h'
  refine (ShortComplex.exact_iff_of_iso ?_).1 h'
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by erw [Category.id_comp, Category.comp_id]; exact hd q)
    (by erw [Category.id_comp, Category.comp_id]; exact hd (q + 1))

end CategoryTheory
