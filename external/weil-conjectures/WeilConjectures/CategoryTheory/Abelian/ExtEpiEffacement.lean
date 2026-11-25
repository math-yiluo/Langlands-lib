/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Effacing individual positive Ext classes in the first variable

Source: Stacks Project, Derived Categories, Tag 06XU.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

/-- A positive Ext class becomes zero after pullback along some epimorphism.
Source: Stacks Project, Derived Categories, Tag 06XU.
(blueprint: lem-sc-ext-epi-effacement)

Proof: follow the fraction construction in the first paragraph of Tag 06XU.
Write the derived morphism representing x as s inverse followed by f, where
s : L -> X[0] is a quasi-isomorphism and f : L -> Y[q]. Take G to be the
object of degree-zero cycles of L. Its map g to X factors as the homology
projection followed by the degree-zero homology isomorphism of s, so g is
epic. The cycle inclusion defines a chain map l : G[0] -> L with l s = g[0].
The composite l f vanishes because Y[q] has zero component in degree zero
when q is positive. Cancelling s in the fraction proves g pulls x back to
zero. All choices remain local witnesses in a theorem, not public data. -/
theorem exists_epi_comp_eq_zero
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {X Y : A} (q : ℕ) (hq : 0 < q) (x : Ext X Y q) :
    ∃ (G : A) (g : G ⟶ X), Epi g ∧ (mk₀ g).comp x (Nat.zero_add q) = 0 := by
  let := HasDerivedCategory.standard A
  let S : CochainComplex A ℤ := (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X
  let T : CochainComplex A ℤ := ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Y)⟦(q : ℤ)⟧
  let e := (DerivedCategory.Q.commShiftIso (q : ℤ)).app
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Y)
  obtain ⟨L, s, hs, f, hfac⟩ := DerivedCategory.right_fac (X := S) (Y := T) (x.hom ≫ e.inv)
  let : IsIso (DerivedCategory.Q.map s) := hs
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso A s).1 hs
  let g : L.cycles 0 ⟶ X := HomologicalComplex.cyclesMap s 0 ≫
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 X).hom
  have hg : Epi g := by
    have heq : g = L.homologyπ 0 ≫ HomologicalComplex.homologyMap s 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := by
      dsimp [g, S]
      rw [HomologicalComplex.homologyπ_naturality_assoc,
        HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
    rw [heq]
    infer_instance
  let l : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (L.cycles 0) ⟶ L :=
    HomologicalComplex.mkHomFromSingle (L.iCycles 0) (fun k _ ↦ L.iCycles_d 0 k)
  have hl : l ≫ s = (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map g := by
    apply HomologicalComplex.from_single_hom_ext
    change (l ≫ s).f 0 =
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map g).f 0
    rw [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self]
    dsimp [l]
    rw [HomologicalComplex.mkHomFromSingle_f]
    dsimp [g]
    rw [HomologicalComplex.singleObjCyclesSelfIso_hom]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Category.assoc] using
      congrArg (fun k ↦
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (L.cycles 0)).hom ≫ k)
        (HomologicalComplex.cyclesMap_i s 0).symm
  have : T.IsStrictlyLE (-(q : ℤ)) :=
    CochainComplex.isStrictlyLE_shift _ 0 _ _ (by omega)
  have hlf : l ≫ f = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    apply (T.isZero_of_isStrictlyLE (-(q : ℤ)) 0 (by omega)).eq_of_tgt
  refine ⟨L.cycles 0, g, hg, ?_⟩
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, Ext.zero_hom, ShiftedHom.mk₀_comp]
  change DerivedCategory.Q.map
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map g) ≫ x.hom = 0
  rw [← hl, DerivedCategory.Q.map_comp]
  have hx : x.hom = (CategoryTheory.inv (DerivedCategory.Q.map s) ≫
      DerivedCategory.Q.map f) ≫ e.hom := by
    rw [← hfac]
    simp [Category.assoc]
  rw [hx]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc, hlf, Functor.map_zero, CategoryTheory.Limits.zero_comp]

end CategoryTheory.Abelian.Ext
