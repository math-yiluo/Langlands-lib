/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Natural-degree deformation retract from split functionals

Source: Stacks Project, Algebra, Tag 00MT, the last three sentences of the proof.
(blueprint: lem-weil-pbc-nat-split-functionals-homotopy)
-/

@[expose] public section
universe u v
open CategoryTheory
namespace ChainComplex

set_option linter.unusedVariables false in
/-- The kernel complement of two split functionals is a deformation retract.
Source: Stacks Project, Algebra, Tag 00MT, proof, the complementary spans.

Proof: Set `S_(j+1)=ker α`, `S_j=ker β`, and `S_k=C_k` elsewhere. Define
the complementary complex by restricting the differentials to these submodules.
The middle differential preserves the kernels by `hd`; the incoming one does
so by `hin`; the remaining codomains are full terms. Their composites vanish
because their inclusions are injective and the original composites vanish.
Define `r_(j+1)(x)=x-α(x)•z`, `r_j(x)=x-β(x)•w`, and `r_k(x)=x` elsewhere.
These maps land in the kernels by `hz` and `hw`. They commute with
differentials: for the incoming differential use `hin`, for the middle one
use `hd` and `hdz`, and for the outgoing one use `hout`. Inclusion `ι` and
`r` satisfy `rι=1` because the functionals vanish on their kernels.
Set the sole nonzero homotopy component, from degree `j` to `j+1`, to
`x ↦ -β(x)•z`. Its two nonzero homotopy equations say that `ιr-1` is
`-α(x)•z` at `j+1` and `-β(x)•w` at `j`, by `hd` and `hdz`; elsewhere
both sides vanish. Together with the zero homotopy for `rι=1`, this defines
the homotopy equivalence from the complement to `C`. The forward map is
the submodule inclusion in each degree and is therefore injective. Identify
the special terms with the two kernels, and the others with the full terms.
When `j=0` there is no outgoing nonzero differential: `C.d 0 0=0` by the
chain shape, so the same construction and equations apply at the boundary.
No finite bases or unit matrix coefficients are used in this construction.
(blueprint: lem-weil-pbc-nat-split-functionals-homotopy) -/
theorem exists_nat_homotopy_equiv_of_split_functionals
    {R : Type u} [CommRing R] (C : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (j : ℕ) (α : C.X (j + 1) →ₗ[R] R) (β : C.X j →ₗ[R] R)
    (z : C.X (j + 1)) (w : C.X j)
    (hz : α z = 1) (hw : β w = 1)
    (hd : ∀ x, β ((C.d (j + 1) j).hom x) = α x)
    (hdz : (C.d (j + 1) j).hom z = w)
    (hin : ∀ x, α ((C.d (j + 2) (j + 1)).hom x) = 0)
    (hout : (C.d j (j - 1)).hom w = 0) :
    let S : ∀ i : ℕ, Submodule R (C.X i) := fun i ↦
      if h : i = j + 1 then h ▸ LinearMap.ker α
      else if h : i = j then h ▸ LinearMap.ker β else ⊤
    ∃ (C' : ChainComplex (ModuleCat.{max u v} R) ℕ)
      (g : ∀ i, C'.X i ≃ₗ[R] S i) (e : HomotopyEquiv C' C),
      ∀ i : ℕ, Function.Injective (e.hom.f i).hom := by
  classical
  let S : ∀ i : ℕ, Submodule R (C.X i) := fun i ↦
    if h : i = j + 1 then h ▸ LinearMap.ker α
    else if h : i = j then h ▸ LinearMap.ker β else ⊤
  let p : ∀ i, C.X i →ₗ[R] C.X i := fun i ↦
    if h : i = j + 1 then h ▸ (LinearMap.id - α.smulRight z)
    else if h : i = j then h ▸ (LinearMap.id - β.smulRight w) else LinearMap.id
  have hj : j ≠ j + 1 := by omega
  have hp_mem : ∀ i (x : C.X i), p i x ∈ S i := by
    intro i x
    by_cases hi : i = j + 1
    · subst i
      simp [S, p, hz]
    by_cases hi' : i = j
    · subst i
      simp [S, p, hw]
    simp [S, hi, hi']
  have hp_fix : ∀ i (x : C.X i), x ∈ S i → p i x = x := by
    intro i x hx
    by_cases hi : i = j + 1
    · subst i
      have hx' : α x = 0 := by simpa [S] using hx
      simp [p, hx']
    by_cases hi' : i = j
    · subst i
      have hx' : β x = 0 := by simpa [S, hj] using hx
      simp [p, hx']
    simp [p, hi, hi']
  have hp_comm : ∀ i k (x : C.X i),
      (C.d i k).hom (p i x) = p k ((C.d i k).hom x) := by
    intro i k x
    by_cases hshape : (ComplexShape.down ℕ).Rel i k
    · have hik : k + 1 = i := hshape
      by_cases hi : i = j + 1
      · have hk : k = j := by omega
        clear hik hshape
        subst i k
        simp [p, map_sub, map_smul, hd, hdz]
      by_cases hi' : i = j
      · have hk : k = j - 1 := by omega
        have hk₁ : k ≠ j + 1 := by omega
        have hk₂ : k ≠ j := by omega
        clear hik hshape
        subst i k
        simp [p, hk₁, hk₂, map_sub, map_smul, hout]
      by_cases hk : k = j + 1
      · have hi₂ : i = j + 2 := by omega
        clear hik hshape
        subst i k
        simp [p, hin]
      have hk' : k ≠ j := by omega
      simp [p, hi, hi', hk, hk']
    · rw [C.shape i k hshape]
      simp
  have hS : ∀ i k (x : C.X i), x ∈ S i → (C.d i k).hom x ∈ S k := by
    intro i k x hx
    rw [← hp_fix i x hx, hp_comm]
    exact hp_mem k _
  let C' : ChainComplex (ModuleCat.{max u v} R) ℕ :=
    { X := fun i ↦ ModuleCat.of R (S i)
      d := fun i k ↦ ModuleCat.ofHom {
        toFun := fun x ↦ ⟨(C.d i k).hom x, hS i k x x.property⟩
        map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
        map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      shape := by
        intro i k h
        ext x
        change (C.d i k).hom x = 0
        rw [C.shape i k h]
        rfl
      d_comp_d' := by
        intro i k l _ _
        ext x
        change (C.d k l).hom ((C.d i k).hom x) = 0
        exact congrArg (fun f ↦ f.hom (x : C.X i)) (C.d_comp_d i k l) }
  let ι : C' ⟶ C :=
    { f := fun i ↦ ModuleCat.ofHom (S i).subtype
      comm' := by intros; rfl }
  let r : C ⟶ C' :=
    { f := fun i ↦ ModuleCat.ofHom ((p i).codRestrict (S i) (hp_mem i))
      comm' := by
        intro i k _
        ext x
        exact hp_comm i k x }
  have hιr : ι ≫ r = 𝟙 C' := by
    ext i x
    exact hp_fix i x x.property
  let s : C.X j ⟶ C.X (j + 1) := ModuleCat.ofHom (-β.smulRight z)
  let h : ∀ i k : ℕ, C.X i ⟶ C.X k := fun i k ↦
    if hi : i = j then
      if hk : k = j + 1 then eqToHom (congrArg C.X hi) ≫ s ≫
        eqToHom (congrArg C.X hk.symm) else 0
    else 0
  have hh : Homotopy (r ≫ ι) (𝟙 C) := by
    refine { hom := h, zero := ?_, comm := ?_ }
    · intro i k hik
      dsimp only [h]
      split_ifs with hi hk
      · subst i k
        exact False.elim (hik rfl)
      · rfl
      · rfl
    · intro i
      rw [dNext_nat, prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)]
      by_cases hi : i = j + 1
      · subst i
        simp only [HomologicalComplex.comp_f, Nat.add_one_sub_one, ↓reduceDIte,
          eqToHom_refl, Category.comp_id, Category.id_comp,
          Nat.add_eq_left, one_ne_zero, Limits.zero_comp, add_zero,
          HomologicalComplex.id_f, h]
        ext x
        change p (j + 1) x = s.hom ((C.d (j + 1) j).hom x) + x
        simp [p, s, hd]
        abel
      by_cases hi' : i = j
      · subst i
        simp only [HomologicalComplex.comp_f, Nat.left_eq_add, one_ne_zero, ↓reduceDIte,
          dite_eq_ite, ite_self, Limits.comp_zero, eqToHom_refl,
          Category.comp_id, Category.id_comp, zero_add, HomologicalComplex.id_f, h]
        ext x
        change p j x = (C.d (j + 1) j).hom (s.hom x) + x
        simp [p, s, map_neg, map_smul, hdz]
        abel
      · simp only [HomologicalComplex.comp_f, hi, ↓reduceDIte, dite_eq_ite, ite_self,
          Limits.comp_zero, hi', Limits.zero_comp, add_zero, HomologicalComplex.id_f,
          zero_add, h]
        ext x
        change p i x = x
        simp [p, hi, hi']
  refine ⟨C', (fun i ↦ LinearEquiv.refl R (S i)),
    ⟨ι, r, Homotopy.ofEq hιr, hh⟩, ?_⟩
  intro i
  exact Subtype.val_injective

end ChainComplex
