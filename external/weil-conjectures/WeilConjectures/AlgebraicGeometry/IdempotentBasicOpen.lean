/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Idempotent global sections and clopen subsets of a scheme

For a scheme `X`, an idempotent global section `e` has germ `0` or `1` at every point, and its
basic open `D(e)` is open and closed. Conversely every open and closed subset of `X` is `D(e)`
for a unique idempotent `e`.

## Main statements

- `AlgebraicGeometry.Scheme.isClopen_basicOpen_of_isIdempotentElem`: `D(e)` is clopen.
- `AlgebraicGeometry.Scheme.eq_of_basicOpen_eq_of_isIdempotentElem`: an idempotent is determined
  by its basic open.
- `AlgebraicGeometry.Scheme.exists_isIdempotentElem_basicOpen_eq`: every clopen subset is the basic
  open of an idempotent.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {e : Γ(X, ⊤)}

/-- The germs of an idempotent global section are `0` or `1`. -/
lemma germ_eq_zero_or_eq_one_of_isIdempotentElem (he : IsIdempotentElem e) (x : X) :
    X.presheaf.germ ⊤ x trivial e = 0 ∨ X.presheaf.germ ⊤ x trivial e = 1 :=
  IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem (he.map (X.presheaf.germ ⊤ x trivial).hom)

/-- A point lies in the basic open of an idempotent global section `e` exactly when the germ
of `e` there is `1`. -/
lemma mem_basicOpen_iff_germ_eq_one_of_isIdempotentElem (he : IsIdempotentElem e) (x : X) :
    x ∈ X.basicOpen e ↔ X.presheaf.germ ⊤ x trivial e = 1 := by
  rw [mem_basicOpen_top]
  rcases germ_eq_zero_or_eq_one_of_isIdempotentElem he x with h | h <;> simp [h]

/-- The basic open of an idempotent global section is open and closed. -/
lemma isClopen_basicOpen_of_isIdempotentElem (he : IsIdempotentElem e) :
    IsClopen (X.basicOpen e : Set X) := by
  have hcompl : (X.basicOpen e : Set X)ᶜ = X.basicOpen (1 - e) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_basicOpen_top, map_sub, map_one]
    rcases germ_eq_zero_or_eq_one_of_isIdempotentElem he x with h | h <;> simp [h]
  exact ⟨isOpen_compl_iff.mp (hcompl ▸ (X.basicOpen (1 - e)).isOpen), (X.basicOpen e).isOpen⟩

/-- An idempotent global section is determined by its basic open. -/
lemma eq_of_basicOpen_eq_of_isIdempotentElem {e' : Γ(X, ⊤)} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (h : X.basicOpen e = X.basicOpen e') : e = e' := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' fun x _ ↦ ?_
  change X.presheaf.germ ⊤ x trivial e = X.presheaf.germ ⊤ x trivial e'
  have hx := (mem_basicOpen_iff_germ_eq_one_of_isIdempotentElem he x).symm.trans
    (h ▸ mem_basicOpen_iff_germ_eq_one_of_isIdempotentElem he' x)
  rcases germ_eq_zero_or_eq_one_of_isIdempotentElem he x with h₁ | h₁ <;>
  rcases germ_eq_zero_or_eq_one_of_isIdempotentElem he' x with h₂ | h₂
  · exact h₁.trans h₂.symm
  · exact absurd (hx.2 h₂) (by rw [h₁]; exact zero_ne_one)
  · exact absurd (hx.1 h₁) (by rw [h₂]; exact zero_ne_one)
  · exact h₁.trans h₂.symm

/-- Every open and closed subset of a scheme is the basic open of an idempotent global section:
the section which is `1` on the subset and `0` on its complement. -/
lemma exists_isIdempotentElem_basicOpen_eq {S : Set X} (hS : IsClopen S) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ (X.basicOpen e : Set X) = S := by
  classical
  let U : X.Opens := ⟨S, hS.isOpen⟩
  let V : X.Opens := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
  have hUV : U ⊔ V = ⊤ := by ext x; simp [U, V]
  have hUV' : U ⊓ V = ⊥ := by ext x; simp [U, V]
  let s : Γ(X, U ⊔ V) := (X.sheaf.objSupIsoProdEqLocus U V).inv ⟨(1, 0),
    TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx ↦ by
      rw [hUV'] at hx; exact absurd hx (by simp)⟩
  let e : Γ(X, ⊤) := X.presheaf.map (eqToHom hUV.symm).op s
  have hsU : X.presheaf.map (homOfLE le_sup_left).op s = 1 :=
    X.sheaf.objSupIsoProdEqLocus_inv_fst U V _
  have hsV : X.presheaf.map (homOfLE le_sup_right).op s = 0 :=
    X.sheaf.objSupIsoProdEqLocus_inv_snd U V _
  have heU : X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op e = 1 := by
    rw [← hsU, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  have heV : X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op e = 0 := by
    rw [← hsV, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  have hgerm (x : X) : X.presheaf.germ ⊤ x trivial e = if x ∈ S then 1 else 0 := by
    split_ifs with hx
    · rw [← X.presheaf.germ_res (homOfLE le_top : U ⟶ ⊤) x hx, CommRingCat.comp_apply, heU,
        map_one]
    · rw [← X.presheaf.germ_res (homOfLE le_top : V ⟶ ⊤) x hx, CommRingCat.comp_apply, heV,
        map_zero]
  have he : IsIdempotentElem e := by
    refine TopCat.Presheaf.section_ext X.sheaf ⊤ _ _ fun x _ ↦ ?_
    change X.presheaf.germ ⊤ x trivial (e * e) = X.presheaf.germ ⊤ x trivial e
    rw [map_mul, hgerm]; split_ifs <;> simp
  refine ⟨e, he, Set.ext fun x ↦ ?_⟩
  rw [SetLike.mem_coe, mem_basicOpen_iff_germ_eq_one_of_isIdempotentElem he, hgerm]
  split_ifs with hx <;> simp [hx]

end AlgebraicGeometry.Scheme
