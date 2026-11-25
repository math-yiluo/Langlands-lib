/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Free
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank

/-! # The invertible pivot in the residue rank-one kernel argument -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace ModuleCat

/-- Source: Stacks Project, Tag 00O0, proof (1), the rank calculation preceding
selection of a unit minor.

Proof: Base change the two finite bases from A to its residue field. Tensor
associativity identifies the resulting map with direct extension of f from R
to the residue field, and the matrix in these bases is obtained by applying
residue to every entry. The assumed kernel equivalence makes the nullity one.
Rank-nullity therefore gives the number of source basis vectors as the matrix
rank plus one. In particular the source cannot have an empty basis. This
argument does not select a minor, lift its determinant, or split coordinates. -/
private theorem residue_kernel_matrix_rank_one
    (R : Type v) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [IsLocalRing A] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (ι κ : Type v) [Fintype ι] [Finite κ] [DecidableEq ι]
    (bX : Module.Basis ι A ((extendScalars (algebraMap R A)).obj X))
    (bY : Module.Basis κ A ((extendScalars (algebraMap R A)).obj Y))
    (hres : Nonempty (LinearMap.ker ((extendScalars
      ((IsLocalRing.residue A).comp (algebraMap R A))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A)) :
    Fintype.card ι =
      ((LinearMap.toMatrix bX bY ((extendScalars (algebraMap R A)).map f).hom).map
        (IsLocalRing.residue A)).rank + 1 := by
  classical
  let F := IsLocalRing.ResidueField A
  let : Algebra A F := (IsLocalRing.residue A).toAlgebra
  let XA := (extendScalars (algebraMap R A)).obj X
  let YA := (extendScalars (algebraMap R A)).obj Y
  let fA := (extendScalars (algebraMap R A)).map f
  let g := (extendScalars (IsLocalRing.residue A)).map fA
  let fF := (extendScalars ((IsLocalRing.residue A).comp (algebraMap R A))).map f
  let E (Z : ModuleCat.{v} A) := tensorEquivExtendScalars A F Z
  let bXF := (Algebra.TensorProduct.basis F bX).map (E XA)
  let bYF := (Algebra.TensorProduct.basis F bY).map (E YA)
  have hmat : LinearMap.toMatrix bXF bYF g.hom =
      (LinearMap.toMatrix bX bY fA.hom).map (IsLocalRing.residue A) := by
    rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
    have hmap : (E YA).symm.toLinearMap ∘ₗ g.hom ∘ₗ (E XA).toLinearMap =
        fA.hom.baseChange F := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s x =>
        apply (E YA).injective
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply]
        change g (tensorEquivExtendScalars A F XA (TensorProduct.tmul A s x)) =
          tensorEquivExtendScalars A F YA (TensorProduct.tmul A s (fA.hom x))
        rw [tensorEquivExtendScalars_tmul, tensorEquivExtendScalars_tmul]
        exact ExtendScalars.map_tmul _ _ _ _
    rw [hmap]
    exact LinearMap.toMatrix_baseChange F fA.hom bX bY
  let α := extendScalarsComp (algebraMap R A) (IsLocalRing.residue A)
  let eX := (α.app X).toLinearEquiv
  let eY := (α.app Y).toLinearEquiv
  have hnat : g.hom ∘ₗ eX.toLinearMap = eY.toLinearMap ∘ₗ fF.hom := by
    exact congrArg Hom.hom (α.hom.naturality f).symm
  have hker : g.hom.ker.comap eX.toLinearMap = fF.hom.ker := by
    rw [← LinearMap.ker_comp, hnat,
      LinearMap.ker_comp_of_ker_eq_bot _ eY.ker]
  let eker : fF.hom.ker ≃ₗ[F] g.hom.ker :=
    (LinearEquiv.ofEq _ _ hker.symm).trans (eX.ofSubmodule' g.hom.ker)
  have hk : Module.finrank F g.hom.ker = 1 := by
    rw [← eker.finrank_eq, hres.some.finrank_eq, Module.finrank_self]
  have : Module.Finite F ((extendScalars (IsLocalRing.residue A)).obj XA) :=
    Module.Finite.of_basis bXF
  have hn := g.hom.finrank_range_add_finrank_ker
  have hd : Module.finrank F ((extendScalars (IsLocalRing.residue A)).obj XA) =
      Fintype.card ι := Module.finrank_eq_card_basis bXF
  rw [hk, hd] at hn
  rw [← hmat, Matrix.rank_eq_finrank_range_toLin _ bYF bXF, Matrix.toLin_toMatrix]
  exact hn.symm

private noncomputable def splitCoordinates
    (A : Type v) [CommRing A] {ι : Type v} {r : ℕ}
    (e : Fin r → ι) (he : Function.Injective e) :
    (ι → A) ≃ₗ[A] ((Fin r → A) × (((Set.range e)ᶜ : Set ι) → A)) := by
  classical
  exact (LinearEquiv.funCongrLeft A A
    ((Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range e)))).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ A A)

private theorem splitCoordinates_symm_inl
    (A : Type v) [CommRing A] {ι : Type v} {r : ℕ}
    (e : Fin r → ι) (he : Function.Injective e)
    (u : Fin r → A) (c : ((Set.range e)ᶜ : Set ι) → A) (i : Fin r) :
    (splitCoordinates A e he).symm (u, c) (e i) = u i := by
  have h := congrArg (fun z ↦ z.1 i)
    ((splitCoordinates A e he).apply_symm_apply (u, c))
  exact h

private theorem splitCoordinates_symm_compl
    (A : Type v) [CommRing A] {ι : Type v} {r : ℕ}
    (e : Fin r → ι) (he : Function.Injective e)
    (u : Fin r → A) (c : ((Set.range e)ᶜ : Set ι) → A) (i : ((Set.range e)ᶜ : Set ι)) :
    (splitCoordinates A e he).symm (u, c) i = c i := by
  have h := congrArg (fun z ↦ z.2 i)
    ((splitCoordinates A e he).apply_symm_apply (u, c))
  exact h

private theorem mulVec_splitCoordinates
    (A : Type v) [CommRing A] {ι κ : Type v} [Fintype ι] {r : ℕ}
    (M : Matrix κ ι A) (rows : Fin r → κ)
    (cols : Fin r → ι) (hc : Function.Injective cols) (u : Fin r → A) (i : Fin r) :
    M.mulVec ((splitCoordinates A cols hc).symm (u, 0)) (rows i) =
      (M.submatrix rows cols).mulVec u i := by
  classical
  let e := (Equiv.sumCongr (Equiv.ofInjective cols hc) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range cols))
  change (∑ j, M (rows i) j * (splitCoordinates A cols hc).symm (u, 0) j) = _
  rw [← e.sum_comp]
  rw [Fintype.sum_sum_type]
  simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply, Sum.map_inr,
    Equiv.Set.sumCompl_apply_inr, Equiv.refl_apply, splitCoordinates_symm_inl,
    splitCoordinates_symm_compl, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- Finite free coordinates with an invertible leading block; the off-diagonal blocks
are unrestricted. Source: Stacks Project, Tags 00O0 and 00NX, unit-minor argument.
(blueprint: new-residue-kernel-unit-minor-pivot)

Proof: Choose finite bases for the two scalar extensions. Tensor associativity
identifies reduction of their matrix modulo the maximal ideal of A with the given
scalar extension to its residue field. Rank-nullity and the kernel equivalence
show that the source dimension n is positive and the matrix rank is n - 1.
Select n - 1 independent columns and n - 1 rows whose square minor has nonzero
determinant. The lifted determinant is a unit of the local ring: its residue is
nonzero. Reorder the selected columns first and the sole remaining column last;
reorder the selected rows first and the complementary rows last. The coordinate
spaces are U = A^(n-1) and C = A^(m-n+1). Take B to be multiplication by the
selected square matrix, with inverse given by its adjugate divided by its unit
determinant. These permutations give eX and eY, and evaluating the leading block
on (u,0) proves the displayed equation. C is free in its coordinate basis. When
n = 1 the leading block is empty, U is zero and B is its identity; no choice of a
nonempty minor is required. The case m < n-1 is excluded by the residue rank.
No elimination of the other three blocks is asserted. -/
theorem residue_kernel_unit_minor_pivot
    (R : Type v) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    [IsLocalRing A] (X Y : ModuleCat.{v} R) (f : X ⟶ Y)
    (hX : Module.Free A
      ((ModuleCat.extendScalars (algebraMap R A)).obj X))
    (hY : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj Y))
    (hfX : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj X))
    (hfY : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj Y))
    (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars
      ((IsLocalRing.residue A).comp (algebraMap R A))).map f).hom
      ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A)) :
    ∃ (U C : ModuleCat.{v} A), Module.Free A C ∧
      ∃ (eX : ((ModuleCat.extendScalars (algebraMap R A)).obj X) ≃ₗ[A] (U × A))
        (eY : ((ModuleCat.extendScalars (algebraMap R A)).obj Y) ≃ₗ[A] (U × C))
        (B : U ≃ₗ[A] U),
        ∀ u, (eY (((ModuleCat.extendScalars (algebraMap R A)).map f).hom
          (eX.symm (u, 0)))).1 = B u := by
  classical
  let := hX
  let := hY
  let := hfX
  let := hfY
  let ι := Module.Free.ChooseBasisIndex A ((extendScalars (algebraMap R A)).obj X)
  let κ := Module.Free.ChooseBasisIndex A ((extendScalars (algebraMap R A)).obj Y)
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  let bX := Module.Free.chooseBasis A ((extendScalars (algebraMap R A)).obj X)
  let bY := Module.Free.chooseBasis A ((extendScalars (algebraMap R A)).obj Y)
  let M := LinearMap.toMatrix bX bY ((extendScalars (algebraMap R A)).map f).hom
  let r := (M.map (IsLocalRing.residue A)).rank
  have hcard : Fintype.card ι = r + 1 :=
    residue_kernel_matrix_rank_one R A X Y f ι κ bX bY hres
  obtain ⟨rows, cols, hdet⟩ :=
    Matrix.exists_submatrix_det_ne_zero_of_le_rank
      (M.map (IsLocalRing.residue A)) (r := r) le_rfl
  have hrows : Function.Injective rows := by
    intro i j hij
    by_contra hne
    apply hdet
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [Matrix.submatrix, hij])
  have hcols : Function.Injective cols := by
    intro i j hij
    by_contra hne
    apply hdet
    exact Matrix.det_zero_of_column_eq hne (by intro k; simp [Matrix.submatrix, hij])
  have hunit : IsUnit (M.submatrix rows cols).det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [RingHom.map_det]
    exact hdet
  let J := (Set.range cols)ᶜ
  let K := (Set.range rows)ᶜ
  have hJ : Fintype.card J = 1 := by
    rw [Fintype.card_compl_set, Fintype.card_congr (Equiv.ofInjective cols hcols).symm,
      Fintype.card_fin, hcard]
    omega
  let : Unique J := (Fintype.card_eq_one_iff_nonempty_unique.mp hJ).some
  let q : (J → A) ≃ₗ[A] A := LinearEquiv.funUnique J A A
  let U : ModuleCat.{v} A := ModuleCat.of A (Fin r → A)
  let C : ModuleCat.{v} A := ModuleCat.of A (K → A)
  let eX : ((extendScalars (algebraMap R A)).obj X) ≃ₗ[A] (U × A) :=
    (bX.equivFun.trans (splitCoordinates A cols hcols)).trans
      ((LinearEquiv.refl A (Fin r → A)).prodCongr q)
  let eY : ((extendScalars (algebraMap R A)).obj Y) ≃ₗ[A] (U × C) :=
    bY.equivFun.trans (splitCoordinates A rows hrows)
  let B : U ≃ₗ[A] U :=
    Matrix.toLinearEquiv (Pi.basisFun A (Fin r)) (M.submatrix rows cols) hunit
  refine ⟨U, C, inferInstance, eX, eY, B, ?_⟩
  intro u
  ext i
  change (bY.equivFun
    (((extendScalars (algebraMap R A)).map f).hom (eX.symm (u, 0)))) (rows i) = _
  rw [Module.Basis.equivFun_apply]
  rw [← LinearMap.toMatrix_mulVec_repr bX bY]
  change M.mulVec (bX.equivFun (eX.symm (u, 0))) (rows i) = _
  have hx : bX.equivFun (eX.symm (u, 0)) =
      (splitCoordinates A cols hcols).symm (u, 0) := by
    dsimp only [eX]
    simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.prodCongr_symm, LinearEquiv.refl_symm]
    congr 1
  rw [hx, mulVec_splitCoordinates]
  change (M.submatrix rows cols).mulVec u i =
    (Matrix.toLin (Pi.basisFun A (Fin r)) (Pi.basisFun A (Fin r))
      (M.submatrix rows cols)) u i
  rw [Matrix.toLin_eq_toLin']
  rfl
end ModuleCat
