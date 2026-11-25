/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Module

/-! # Contracting a split two-term identity complex

Source: Stacks Project, Tag 00MT, the identity summand and its contraction.
(blueprint: lem-pc-split-identity-homotopy-equiv)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped DirectSum
namespace ChainComplex

set_option backward.isDefEq.respectTransparency.types false in
private def binarySumEquiv {R : Type u} [CommRing R] (X Y : ModuleCat.{u} R) :
    (⨁ s : Bool, ((fun s : Bool ↦ if s then Y else X) s : ModuleCat.{u} R)) ≃ₗ[R]
      (X × Y) where
  toFun z := (z false, z true)
  invFun z := DFinsupp.single false z.1 + DFinsupp.single true z.2
  left_inv z := by
    apply DFinsupp.ext
    intro s
    cases s <;> dsimp [DirectSum] at * <;> simp only [DFinsupp.single_eq_same,
      DFinsupp.single_eq_of_ne Bool.false_ne_true,
      DFinsupp.single_eq_of_ne (Ne.symm Bool.false_ne_true), add_zero, zero_add]
  right_inv z := by
    dsimp [DirectSum] at *
    simp only [DFinsupp.single_eq_same,
      DFinsupp.single_eq_of_ne Bool.false_ne_true,
      DFinsupp.single_eq_of_ne (Ne.symm Bool.false_ne_true), add_zero, zero_add]
  map_add' z w := rfl
  map_smul' r z := rfl

private theorem contractIdentity {R : Type u} [CommRing R]
    (T : ChainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (hT : ∀ j : ℤ, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j))
    (e : T.X i ≃ₗ[R] R) (f : T.X (i - 1) ≃ₗ[R] R)
    (hef : ∀ t : T.X i, f ((T.d i (i - 1)).hom t) = e t) :
    Nonempty (Homotopy (𝟙 T) 0) := by
  classical
  let s : T.X (i - 1) ⟶ T.X i :=
    ModuleCat.ofHom (e.symm.toLinearMap.comp f.toLinearMap)
  have hds : T.d i (i - 1) ≫ s = 𝟙 _ := by
    ext t
    change e.symm (f ((T.d i (i - 1)).hom t)) = t
    rw [hef, e.symm_apply_apply]
  have hsd : s ≫ T.d i (i - 1) = 𝟙 _ := by
    ext t
    apply f.injective
    change f ((T.d i (i - 1)).hom (e.symm (f t))) = f t
    rw [hef, e.apply_symm_apply]
  let h : ∀ j k : ℤ, T.X j ⟶ T.X k := fun j k ↦
    if hj : j = i - 1 then
      if hk : k = i then eqToHom (congrArg T.X hj) ≫ s ≫
        eqToHom (congrArg T.X hk.symm) else 0
    else 0
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro j k hjk
    dsimp only [h]
    split_ifs with hj hk
    · subst j k
      exact False.elim (hjk (by change i - 1 + 1 = i; omega))
    · rfl
    · rfl
  · intro j
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j - 1) by
      change j - 1 + 1 = j; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j + 1) j from rfl)]
    by_cases hj : j = i
    · subst j
      have hi : i ≠ i - 1 := by omega
      simp [h, hi, hds]
    · by_cases hj₁ : j = i - 1
      · subst j
        have hi : i - 1 + 1 = i := by omega
        have hi₂ : i - 1 - 1 ≠ i - 1 := by omega
        simp [h, hi, hi₂, hsd]
      · ext x
        exact (hT j hj hj₁).elim _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Projection away from a differential-compatible split identity complex is a homotopy
 equivalence. Source: Stacks Project, Tag 00MT, the two-term identity summand.
(blueprint: lem-pc-split-identity-homotopy-equiv)

Proof: Use ψ to define the projection C → C' and the inclusion C' → C degreewise.
The compatibility equation, first with t = 0 and then x = 0, proves these are chain
maps. Their composite on C' is the identity. On T define h from degree i-1 to degree i
as e.symm ∘ f and zero for all other pairs. The equation f(d t) = e t implies both
inverse identities for d. Thus d h + h d is the identity at i and i-1. At every other
degree T is subsingleton, so the identity and all relevant morphisms are zero.
Transport minus this contraction along the T inclusion and projection through ψ.
It is a homotopy from the C' projection-inclusion composite to the identity on C,
since that composite equals identity minus the T projector. Together with the exact
identity on C' this gives the asserted homotopy equivalence. No basis, rank, unit
coefficient, or affine sheaf comparison is used in this lemma. The argument works
in the zero ring and when C' is zero in either or both special degrees. -/
theorem nonempty_homotopyEquiv_of_split_identity
    {R : Type u} [CommRing R] (C C' T : ChainComplex (ModuleCat.{u} R) ℤ)
    (i : ℤ) (hT : ∀ j : ℤ, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j))
    (e : T.X i ≃ₗ[R] R) (f : T.X (i - 1) ≃ₗ[R] R)
    (hef : ∀ t : T.X i, f ((T.d i (i - 1)).hom t) = e t)
    : let M : ℤ → Bool → ModuleCat.{u} R :=
        fun j s ↦ if s then T.X j else C'.X j
      ∀ (ψ : ∀ j : ℤ, (⨁ s : Bool, M j s) ≃ₗ[R] C.X j)
    (_hψ : ∀ (j : ℤ) (x : C'.X j) (t : T.X j),
      (C.d j (j - 1)).hom
          (ψ j (DirectSum.lof R Bool (fun s ↦ M j s) false x +
            DirectSum.lof R Bool (fun s ↦ M j s) true t)) =
        ψ (j - 1)
          (DirectSum.lof R Bool (fun s ↦ M (j - 1) s) false
              ((C'.d j (j - 1)).hom x) +
            DirectSum.lof R Bool (fun s ↦ M (j - 1) s) true
              ((T.d j (j - 1)).hom t))),
      Nonempty (HomotopyEquiv C C') := by
  classical
  dsimp only
  intro ψ hψ
  let g : ∀ j : ℤ, (C'.X j × T.X j) ≃ₗ[R] C.X j :=
    fun j ↦ (binarySumEquiv (C'.X j) (T.X j)).symm.trans (ψ j)
  have hg : ∀ j (x : C'.X j) (t : T.X j),
      (C.d j (j - 1)).hom (g j (x, t)) =
        g (j - 1) ((C'.d j (j - 1)).hom x, (T.d j (j - 1)).hom t) := by
    intro j x t
    exact hψ j x t
  have hgd : ∀ j (y : C.X j),
      (g (j - 1)).symm ((C.d j (j - 1)).hom y) =
        ((C'.d j (j - 1)).hom ((g j).symm y).1,
          (T.d j (j - 1)).hom ((g j).symm y).2) := by
    intro j y
    apply (g (j - 1)).injective
    simpa only [LinearEquiv.apply_symm_apply, Prod.mk.eta] using
      hg j ((g j).symm y).1 ((g j).symm y).2
  let π : C ⟶ C' :=
    { f := fun j ↦ ModuleCat.ofHom
        ((LinearMap.fst R (C'.X j) (T.X j)).comp (g j).symm.toLinearMap)
      comm' := by
        intro j k hjk
        have hk : k = j - 1 := by change k + 1 = j at hjk; omega
        subst k
        ext y
        exact (congrArg Prod.fst (hgd j y)).symm }
  let ι : C' ⟶ C :=
    { f := fun j ↦ ModuleCat.ofHom
        ((g j).toLinearMap.comp (LinearMap.inl R (C'.X j) (T.X j)))
      comm' := by
        intro j k hjk
        have hk : k = j - 1 := by change k + 1 = j at hjk; omega
        subst k
        ext x
        change (C.d j (j - 1)).hom (g j (x, 0)) =
          g (j - 1) ((C'.d j (j - 1)).hom x, 0)
        simpa only [map_zero] using hg j x 0 }
  let πT : C ⟶ T :=
    { f := fun j ↦ ModuleCat.ofHom
        ((LinearMap.snd R (C'.X j) (T.X j)).comp (g j).symm.toLinearMap)
      comm' := by
        intro j k hjk
        have hk : k = j - 1 := by change k + 1 = j at hjk; omega
        subst k
        ext y
        exact (congrArg Prod.snd (hgd j y)).symm }
  let ιT : T ⟶ C :=
    { f := fun j ↦ ModuleCat.ofHom
        ((g j).toLinearMap.comp (LinearMap.inr R (C'.X j) (T.X j)))
      comm' := by
        intro j k hjk
        have hk : k = j - 1 := by change k + 1 = j at hjk; omega
        subst k
        ext t
        change (C.d j (j - 1)).hom (g j (0, t)) =
          g (j - 1) (0, (T.d j (j - 1)).hom t)
        simpa only [map_zero] using hg j 0 t }
  have hπι : ι ≫ π = 𝟙 C' := by
    ext j x
    change ((g j).symm (g j (x, 0))).1 = x
    rw [LinearEquiv.symm_apply_apply]
  have hsum : π ≫ ι + πT ≫ ιT = 𝟙 C := by
    ext j y
    change g j (((g j).symm y).1, 0) + g j (0, ((g j).symm y).2) = y
    rw [← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using
      (g j).apply_symm_apply y
  obtain ⟨ht⟩ := contractIdentity T i hT e f hef
  have hh : Homotopy (πT ≫ ιT) 0 := by
    simpa only [Category.comp_id, Category.id_comp, Category.assoc,
      comp_zero, zero_comp] using (ht.compLeft πT).compRight ιT
  have hh' : Homotopy (𝟙 C) (π ≫ ι) := by
    simpa only [hsum, add_zero] using (Homotopy.refl (π ≫ ι)).add hh
  exact ⟨⟨π, ι, hh'.symm, Homotopy.ofEq hπι⟩⟩

end ChainComplex
