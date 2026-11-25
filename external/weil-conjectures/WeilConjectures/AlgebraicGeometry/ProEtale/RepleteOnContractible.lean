/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RepleteSheafTopos
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Sequential limits on weakly contractible pro-étale objects

## Implementation details

Sheaves take values in `Type (max (u + 1) w)`, allowing arbitrarily large sets without equating
the object and morphism universes of the site.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Every transition and every limit projection of an epimorphic inverse sequence is
surjective on sections over a weakly contractible object `W` (one at which epimorphisms of
sheaves induce surjections on sections). -/
theorem proetale_surjective_sections_of_epi_tower
    (X : Scheme.{u}) (F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) (Type (max (u + 1) w)))
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (W : X.ProEt) (hW : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) w} W) :
    (∀ n : ℕ,
      Function.Surjective ((F.map (homOfLE (Nat.le_succ n)).op).hom.app (op W))) ∧
    (∀ m : ℕ, Function.Surjective ((limit.π F (op m)).hom.app (op W))) := by
  classical
  have hs (n : ℕ) :
      Function.Surjective ((F.map (homOfLE (Nat.le_succ n)).op).hom.app (op W)) := by
    have := hF n
    exact hW _ ((Sheaf.isLocallySurjective_iff_epi _).2 inferInstance)
  refine ⟨hs, ?_⟩
  let ev := sheafToPresheaf (ProEt.topology X) (Type (max (u + 1) w)) ⋙
    (CategoryTheory.evaluation X.ProEtᵒᵖ (Type (max (u + 1) w))).obj (op W)
  let G := F ⋙ ev
  have hG (n : ℕ) : Function.Surjective (G.map (homOfLE (Nat.le_succ n)).op) := hs n
  intro m a
  let x : (n : ℕ) → G.obj (op n) := Nat.rec
    (G.map (homOfLE (Nat.zero_le m)).op a)
    (fun n prev ↦ if h : n + 1 ≤ m then G.map (homOfLE h).op a
      else (hG n prev).choose)
  have hx (n : ℕ) (h : n ≤ m) : x n = G.map (homOfLE h).op a := by
    cases n with
    | zero => rfl
    | succ n => exact dite_eq_left h
  have hstep (n : ℕ) : G.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n := by
    by_cases h : n + 1 ≤ m
    · rw [hx (n + 1) h, hx n (Nat.le_trans (Nat.le_succ n) h)]
      rw [← types_comp_apply, ← G.map_comp]
      rfl
    · change G.map (homOfLE (Nat.le_succ n)).op
        (if h : n + 1 ≤ m then G.map (homOfLE h).op a
          else (hG n (x n)).choose) = x n
      rw [dite_eq_right h]
      exact (hG n (x n)).choose_spec
  have hcompat (n k : ℕ) (h : k ≤ n) : G.map (homOfLE h).op (x n) = x k := by
    induction h with
    | refl => simp
    | @step n h ih =>
      have heq : (homOfLE (Nat.le_trans h (Nat.le_succ n))).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op := rfl
      rw [heq, G.map_comp, types_comp_apply, hstep, ih]
  let s : G.sections := ⟨fun j ↦ x j.unop, by
    intro i j f
    exact hcompat i.unop j.unop (leOfHom f.unop)⟩
  let hc := isLimitOfPreserves ev (limit.isLimit F)
  refine ⟨(Types.isLimitEquivSections hc).symm s, ?_⟩
  change (ev.mapCone (limit.cone F)).π.app (op m)
    ((Types.isLimitEquivSections hc).symm s) = a
  calc
    _ = x m := Types.isLimitEquivSections_symm_apply hc s (op m)
    _ = a := by
      rw [hx m le_rfl]
      simp

end AlgebraicGeometry.Scheme
