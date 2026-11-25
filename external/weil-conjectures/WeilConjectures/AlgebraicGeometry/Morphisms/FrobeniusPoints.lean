/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-!
# The Frobenius on points with values in an algebra

Let `k` be a finite field with `q` elements, `X` a scheme over `k` and `F` its `q`-power
Frobenius. For a `k`-algebra `R`, a morphism `t : Spec R ⟶ X` and `m : ℕ`, composing `t` with
the iterate `F^m` is the same as precomposing it with `Spec` of the `m`-th power of the
Frobenius `k`-algebra endomorphism `r ↦ r ^ q` of `R`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.IsFrobenius.comp_pow_eq_specMap_frobeniusAlgHom_pow`:
  `t ≫ F^m = Spec (Frob_R^m) ≫ t`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom.IsFrobenius

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} {F : X ⟶ X}

/-- For the `#k`-power Frobenius `F` of a scheme `X` over `Spec k` and a `k`-algebra `R`, a
morphism `t : Spec R ⟶ X` satisfies `t ≫ F^m = Spec (Frob_R^m) ≫ t`, where `Frob_R` is the
Frobenius `k`-algebra endomorphism `r ↦ r ^ #k` of `R`. -/
lemma comp_pow_eq_specMap_frobeniusAlgHom_pow (hF : F.IsFrobenius (Nat.card k))
    (f₀ : X ⟶ Spec (.of k)) {R : Type u} [CommRing R] [Algebra k R] (t : Spec (.of R) ⟶ X)
    (m : ℕ) :
    t ≫ End.asHom (End.of F ^ m) =
      Spec.map (CommRingCat.ofHom
        ((FiniteField.frobeniusAlgHom k R ^ m : R →ₐ[k] R) : R →+* R)) ≫ t := by
  refine hF.pow f₀ m t _ fun r ↦ ?_
  change (FiniteField.frobeniusAlgHom k R ^ m) r = r ^ Nat.card k ^ m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.frobeniusAlgHom_apply, ← pow_mul,
      Nat.card_eq_fintype_card, pow_succ]

end AlgebraicGeometry.Scheme.Hom.IsFrobenius
