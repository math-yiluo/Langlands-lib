/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius

/-!
# The absolute Frobenius and morphisms to `Spec LC(S, ℤ)`

Let `p` be a prime. Every locally constant function `f : S → ℤ` satisfies
`f ^ p ^ n ≡ f` modulo `p` (Fermat's little theorem, pointwise). Consequently, for a scheme `V`
in which `p` vanishes, the `p ^ n`-power absolute Frobenius `F_V` is invisible to morphisms
`V ⟶ Spec LC(S, ℤ)`: `F_V ≫ g = g`.

## Main results

- `LocallyConstant.exists_pow_prime_pow_sub_eq_mul`: `f ^ p ^ n - f ∈ p • LC(S, ℤ)`.
- `AlgebraicGeometry.Scheme.iterateFrobenius_comp_of_forall_exists_pow_sub_eq_mul`: if every
  element `r` of `R` satisfies `r ^ p ^ n - r ∈ p R`, then `F_V ≫ g = g` for every morphism
  `g : V ⟶ Spec R` from a scheme `V` in which `p` vanishes.
- `AlgebraicGeometry.Scheme.iterateFrobenius_comp_locallyConstant`: the case
  `R = LC(S, ℤ)`.
-/

@[expose] public section

universe u

open CategoryTheory

/-- **Fermat's little theorem** for locally constant integer-valued functions: `f ^ p ^ n - f`
is divisible by the prime `p`. -/
lemma LocallyConstant.exists_pow_prime_pow_sub_eq_mul {S : Type*} [TopologicalSpace S]
    {p : ℕ} (hp : p.Prime) (n : ℕ) (f : LocallyConstant S ℤ) :
    ∃ g : LocallyConstant S ℤ, f ^ p ^ n - f = p * g := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd (z : ℤ) : (p : ℤ) ∣ z ^ p ^ n - z := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card_pow, sub_self]
  refine ⟨f.map fun z ↦ (z ^ p ^ n - z) / p, ?_⟩
  ext x
  exact (Int.mul_ediv_cancel' (hdvd (f x))).symm

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} (hp : p.Prime) (n : ℕ)

/-- If every element `r` of a ring `R` satisfies `r ^ p ^ n ≡ r` modulo `p`, then the
`p ^ n`-power absolute Frobenius of a scheme `V` in which `p` vanishes does not change
morphisms `g : V ⟶ Spec R`: on global sections, `F_V ≫ g` is `r ↦ g(r) ^ p ^ n = g(r)`. -/
lemma iterateFrobenius_comp_of_forall_exists_pow_sub_eq_mul {R : CommRingCat.{u}}
    (hR : ∀ r : R, ∃ s : R, r ^ p ^ n - r = p * s) {V : Scheme.{u}} (hV : (p : Γ(V, ⊤)) = 0)
    (g : V ⟶ Spec R) : V.iterateFrobenius hp hV n ≫ g = g := by
  refine ext_of_isAffine ?_
  rw [Hom.comp_appTop, ← cancel_epi (ΓSpecIso R).inv]
  ext r
  obtain ⟨s, hs⟩ := hR r
  have h := congr(((ΓSpecIso R).inv ≫ g.appTop).hom $hs)
  rw [map_sub, map_pow, map_mul, map_natCast, hV, zero_mul, sub_eq_zero] at h
  exact h

/-- The `p ^ n`-power absolute Frobenius of a scheme `V` in which `p` vanishes does not change
morphisms `g : V ⟶ Spec LC(S, ℤ)`. -/
lemma iterateFrobenius_comp_locallyConstant {S : Type u} [TopologicalSpace S]
    {V : Scheme.{u}} (hV : (p : Γ(V, ⊤)) = 0) (g : V ⟶ Spec (.of (LocallyConstant S ℤ))) :
    V.iterateFrobenius hp hV n ≫ g = g :=
  iterateFrobenius_comp_of_forall_exists_pow_sub_eq_mul hp n
    (LocallyConstant.exists_pow_prime_pow_sub_eq_mul hp n) hV g

end AlgebraicGeometry.Scheme
