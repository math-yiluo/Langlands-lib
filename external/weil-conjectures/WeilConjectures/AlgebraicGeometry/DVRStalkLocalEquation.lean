/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Local equations at a point with a discrete valuation ring as local ring

Let `Y` be a scheme and `y` a point whose local ring `𝒪_{Y,y}` is a discrete valuation ring (for
instance a point of codimension one of a normal scheme). If `p` is a section near `y` whose germ is
a uniformizer, every section `h` with nonzero germ is, on a neighbourhood of `y`, a unit times a
power `p^n` (`AlgebraicGeometry.Scheme.exists_span_eq_span_pow_of_irreducible_germ`), and `n ≥ 1`
when `h` vanishes at `y`. This is the "shrink around a generic point of the divisor" step of
blueprint `lemma-vanishing-generic-points-principal-divisor`: near `ζ`, `V(h) = V(p^n)`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- **Local equations at a point with a discrete valuation ring as local ring**: let `y` be a point
of `Y` with `𝒪_{Y,y}` a discrete valuation ring, and `h`, `p` sections over an open `U ∋ y` such
that the germ of `h` is nonzero and the germ of `p` is a uniformizer. Then on some open
`y ∈ W ⊆ U`, `h|_W = s · (p|_W)^n` for a unit `s` and some `n`, so that `(h|_W) = (p|_W^n)` as
ideals. If moreover `h` vanishes at `y` (its germ is not a unit), then `n ≥ 1`. -/
theorem exists_span_eq_span_pow_of_irreducible_germ {Y : Scheme.{u}} {y : Y}
    [IsDomain (Y.presheaf.stalk y)] [IsDiscreteValuationRing (Y.presheaf.stalk y)] {U : Y.Opens}
    (hyU : y ∈ U) (h p : Γ(Y, U))
    (hh : Y.presheaf.germ U y hyU h ≠ 0) (hp : Irreducible (Y.presheaf.germ U y hyU p))
    (hhy : ¬ IsUnit (Y.presheaf.germ U y hyU h)) :
    ∃ (W : Y.Opens) (_ : y ∈ W) (iW : W ⟶ U) (n : ℕ), 0 < n ∧
      Ideal.span {Y.presheaf.map iW.op h} = Ideal.span {Y.presheaf.map iW.op p ^ n} := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hh hp
  have hn : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn ↦ hhy ?_
    rw [hn, pow_zero] at hu
    exact IsUnit.of_mul_eq_one _ hu
  obtain ⟨U₁, hy₁, s, hs⟩ := Y.presheaf.exists_germ_eq (u : Y.presheaf.stalk y)
  obtain ⟨U₂, hy₂, t, ht⟩ := Y.presheaf.exists_germ_eq (↑u⁻¹ : Y.presheaf.stalk y)
  -- `h * s = p ^ n` near `y`
  have e₁ : Y.presheaf.germ (U ⊓ U₁) y ⟨hyU, hy₁⟩
      (Y.presheaf.map (homOfLE inf_le_left).op h * Y.presheaf.map (homOfLE inf_le_right).op s) =
      Y.presheaf.germ U y hyU (p ^ n) := by
    rw [map_mul, map_pow, Y.presheaf.germ_res_apply, Y.presheaf.germ_res_apply, hs, hu]
  -- `s * t = 1` near `y`
  have e₂ : Y.presheaf.germ (U₁ ⊓ U₂) y ⟨hy₁, hy₂⟩
      (Y.presheaf.map (homOfLE inf_le_left).op s * Y.presheaf.map (homOfLE inf_le_right).op t) =
      Y.presheaf.germ U₁ y hy₁ 1 := by
    rw [map_mul, map_one, Y.presheaf.germ_res_apply, Y.presheaf.germ_res_apply, hs, ht,
      Units.mul_inv]
  obtain ⟨W₁, hW₁, a₁, b₁, f₁⟩ := Y.presheaf.germ_eq y _ _ _ _ e₁
  obtain ⟨W₂, hW₂, a₂, b₂, f₂⟩ := Y.presheaf.germ_eq y _ _ _ _ e₂
  refine ⟨W₁ ⊓ W₂, ⟨hW₁, hW₂⟩, homOfLE inf_le_left ≫ b₁, n, hn, ?_⟩
  set r₁ : W₁ ⊓ W₂ ⟶ W₁ := homOfLE inf_le_left
  set r₂ : W₁ ⊓ W₂ ⟶ W₂ := homOfLE inf_le_right
  have f₁' := congrArg (Y.presheaf.map r₁.op) f₁
  have f₂' := congrArg (Y.presheaf.map r₂.op) f₂
  simp only [map_mul, map_pow, map_one, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← op_comp] at f₁' f₂'
  have hunit : IsUnit (Y.presheaf.map (r₁ ≫ a₁ ≫ homOfLE inf_le_right).op s) := by
    refine IsUnit.of_mul_eq_one (Y.presheaf.map (r₂ ≫ a₂ ≫ homOfLE inf_le_right).op t) ?_
    convert f₂' using 3
  rw [← Ideal.span_singleton_mul_right_unit hunit]
  convert congrArg (fun x ↦ Ideal.span {x}) f₁' using 4

end AlgebraicGeometry.Scheme
