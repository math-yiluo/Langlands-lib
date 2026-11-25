/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison
import WeilConjectures.CategoryTheory.Abelian.SplitSESCocycleBoundary

/-!
# Injective-resolution and derived connecting morphisms agree

Source: Stacks Project, Derived Categories, Tags 05TE and 06XR
(blueprint: lem-sc-p1-ext-resolution-derived-connecting).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The injective-resolution boundary, computed by lifting a cocycle and taking its
 differential, agrees with the boundary of the distinguished short-exact-sequence triangle.
Source: Stacks Project, Derived Categories, Tags 05TE and 06XR
(blueprint: lem-sc-p1-ext-resolution-derived-connecting).

Here `i`, `p`, `hιi`, `hιp`, and `hexact` describe any horseshoe resolution of `S`.
For a cocycle `c`, choose a lift `b` through `p`, and factor its differential as `a ≫ i`.
The resolution connecting map sends the class of `c` to the class of `a`. Degreewise
short exactness splits because the first resolution is injective, so all these lifts exist.
The constructor `extMk` is the inverse of the canonical Ext/cohomology-class comparison.
Thus the equation below is equality of the two connecting maps on every class, with
all choices of representatives and lifts allowed, including in degree zero.

Proof: Extend the horseshoe to integer degrees and split each row, transporting the
injective-kernel splittings through the canonical degree isomorphisms. Below zero use
the zero splitting. The augmentations give a morphism of short exact rows. Apply
triangleOfSESδ_naturality and lem-sc-p1-split-ses-boundary-comparison to identify the
single-object boundary with the split boundary after the augmentations. Transport
c,b,a to integer degrees and apply lem-sc-p1-split-ses-cocycle-boundary. Finally rewrite
extMk_hom as its cocycle roof and homologySequenceδ as shifted composition. Invert the
augmentation maps and use associativity of shifted composition to obtain the equation. -/
theorem extMk_resolution_connecting_eq_triangle
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {S : ShortComplex C} (hS : S.ShortExact) (M : C)
    (RA : InjectiveResolution S.X₁) (RB : InjectiveResolution S.X₂)
    (RC : InjectiveResolution S.X₃)
    (i : RA.cocomplex ⟶ RB.cocomplex) (p : RB.cocomplex ⟶ RC.cocomplex)
    (hip : i ≫ p = 0)
    (hιi : RA.ι ≫ i = (CochainComplex.single₀ C).map S.f ≫ RB.ι)
    (hιp : RB.ι ≫ p = (CochainComplex.single₀ C).map S.g ≫ RC.ι)
    (hexact : ∀ k : ℕ,
      ((ShortComplex.mk i p hip).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) k)).ShortExact)
    (n : ℕ) (c : M ⟶ RC.cocomplex.X n)
    (hc : c ≫ RC.cocomplex.d n (n + 1) = 0)
    (b : M ⟶ RB.cocomplex.X n) (hb : b ≫ p.f n = c)
    (a : M ⟶ RA.cocomplex.X (n + 1))
    (ha : a ≫ RA.cocomplex.d (n + 1) (n + 1 + 1) = 0)
    (hba : b ≫ RB.cocomplex.d n (n + 1) = a ≫ i.f (n + 1)) :
    letI := HasExt.standard C
    letI := HasDerivedCategory.standard C
    (preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor C 0).obj M))).homologySequenceδ
        hS.singleTriangle (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)
        (RC.extMk c (n + 1) rfl hc).hom =
      (RA.extMk a (n + 1 + 1) rfl ha).hom := by
  classical
  let := HasExt.standard C
  let := HasDerivedCategory.standard C
  let fi : Hom RA RB S.f := ⟨i, by simpa using congrArg (fun f ↦ f.f 0) hιi⟩
  let gp : Hom RB RC S.g := ⟨p, by simpa using congrArg (fun f ↦ f.f 0) hιp⟩
  have hip' : fi.hom' ≫ gp.hom' = 0 := by
    dsimp [fi, gp, Hom.hom']
    rw [← HomologicalComplex.extendMap_comp, hip, HomologicalComplex.extendMap_zero]
  let T : ShortComplex (CochainComplex C ℤ) := ShortComplex.mk fi.hom' gp.hom' hip'
  let σ (k : ℤ) : (T.map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) k)).Splitting := by
    by_cases hk : 0 ≤ k
    · let j := k.toNat
      have hj : (j : ℤ) = k := Int.toNat_of_nonneg hk
      let e : (T.map (HomologicalComplex.eval C (ComplexShape.up ℤ) k)) ≅
          ((ShortComplex.mk i p hip).map
            (HomologicalComplex.eval C (ComplexShape.up ℕ) j)) :=
        ShortComplex.isoMk (RA.cochainComplexXIso k j hj)
          (RB.cochainComplexXIso k j hj) (RC.cochainComplexXIso k j hj)
          (by simp [T, Hom.hom'_f fi k j hj, fi])
          (by simp [T, Hom.hom'_f gp k j hj, gp])
      have : Injective (((ShortComplex.mk i p hip).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) j)).X₁) := by
        change Injective (RA.cocomplex.X j)
        infer_instance
      exact (hexact j).splittingOfInjective.ofIso e.symm
    · have h₁ := CochainComplex.isZero_of_isStrictlyGE RA.cochainComplex 0 k (by omega)
      have h₂ := CochainComplex.isZero_of_isStrictlyGE RB.cochainComplex 0 k (by omega)
      have h₃ := CochainComplex.isZero_of_isStrictlyGE RC.cochainComplex 0 k (by omega)
      exact
        { r := 0
          s := 0
          f_r := h₁.eq_of_src _ _
          s_g := h₃.eq_of_src _ _
          id := h₂.eq_of_src _ _ }
  have hT : T.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact T (fun k ↦ (σ k).shortExact)
  let F : S.map (CochainComplex.singleFunctor C 0) ⟶ T :=
    { τ₁ := RA.ι'
      τ₂ := RB.ι'
      τ₃ := RC.ι'
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T] }
  have hδ := DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) hT F
  rw [DerivedCategory.triangleOfSESδ_eq_degreewiseSplit T hT σ] at hδ
  let c' := c ≫ (RC.cochainComplexXIso n n rfl).inv
  let b' := b ≫ (RB.cochainComplexXIso n n rfl).inv
  let a' := a ≫ (RA.cochainComplexXIso (n + 1) (n + 1) (by simp)).inv
  have hc' : c' ≫ RC.cochainComplex.d n (n + 1) = 0 := by
    simp [c', RC.cochainComplex_d n (n + 1) n (n + 1) rfl (by simp), reassoc_of% hc]
  have ha' : a' ≫ RA.cochainComplex.d (n + 1) (n + 1 + 1) = 0 := by
    simp [a', RA.cochainComplex_d (n + 1) (n + 1 + 1) (n + 1) (n + 1 + 1) (by simp) (by simp),
      reassoc_of% ha]
  have hb' : b' ≫ T.g.f n = c' := by
    simp [b', c', T, Hom.hom'_f gp n n rfl, gp, Category.assoc, reassoc_of% hb]
  have hba' : b' ≫ T.X₂.d n (n + 1) = a' ≫ T.f.f (n + 1) := by
    simp [b', a', T, Hom.hom'_f fi (n + 1) (n + 1) (by simp), fi,
      RB.cochainComplex_d n (n + 1) n (n + 1) rfl (by simp), Category.assoc, reassoc_of% hba]
  have hcomp := CochainComplex.degreewiseSplit_cocycle_boundary T σ M n c' hc'
    b' hb' a' ha' hba'
  dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors] at hδ hcomp
  have hsingle : hS.singleδ ≫ (DerivedCategory.Q.map RA.ι')⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map RC.ι' ≫
        ShiftedHom.map (CochainComplex.homOfDegreewiseSplit T σ) DerivedCategory.Q := by
    simpa [ShortComplex.ShortExact.singleδ, SingleFunctors.evaluation,
      Functor.mapIso, SingleFunctors.postcomp, CochainComplex.singleFunctors,
      DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
      DerivedCategory.singleFunctorsPostcompQIso_inv_hom, NatTrans.id_app,
      Functor.map_id, Category.id_comp, Category.comp_id, Functor.comp_obj, F] using hδ
  have hinv : (ShiftedHom.mk₀ (0 : ℤ) rfl
      (inv (DerivedCategory.Q.map RC.ι'))).comp hS.singleδ (add_zero 1) =
      (ShiftedHom.map (CochainComplex.homOfDegreewiseSplit T σ) DerivedCategory.Q).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (DerivedCategory.Q.map RA.ι'))) (zero_add 1) := by
    simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
    dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    rw [Functor.map_inv (shiftFunctor (DerivedCategory C) (1 : ℤ)),
      eq_comm]
    erw [IsIso.comp_inv_eq]
    rw [Category.assoc, eq_comm]
    erw [IsIso.inv_comp_eq]
    exact hsingle
  rw [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply]
  change ((RC.extMk c (n + 1) rfl hc).hom).comp hS.singleδ
    (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega) = _
  simp only [extMk_hom, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, ShiftedHom.mk₀_id_comp,
    CochainComplex.singleFunctor,
    DerivedCategory.Q_obj_single_obj, Category.comp_id] at ⊢
  rw [ShiftedHom.comp_assoc _ _ _ (zero_add _) (add_zero _) (by omega), hinv,
    ← ShiftedHom.comp_assoc _ _ _
      (show (1 : ℤ) + n = ((n + 1 : ℕ) : ℤ) by omega) (zero_add _) (by omega)]
  convert congrArg (fun z ↦ z.comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (DerivedCategory.Q.map RA.ι')))
    (zero_add (n + 1 : ℤ))) hcomp using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, c', a', CochainComplex.singleFunctor,
      DerivedCategory.Q_obj_single_obj] <;>
      rfl

end CategoryTheory.InjectiveResolution
