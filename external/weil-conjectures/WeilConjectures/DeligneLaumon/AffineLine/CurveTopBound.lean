/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CurveEndpoints
public import WeilConjectures.DeligneLaumon.Reduction.AffineCurve

/-!
# The top compactly supported cohomology of a lisse sheaf on a smooth affine curve

If `C₀` is a smooth affine curve and `G` is a lisse Weil sheaf on `C₀`, punctually `ι`-pure of
weight `w`, then `H_c^2(C, G)` has weights at most `w + 2` (blueprint
`lemma-degree-zero-top-cohomology--6`). It follows from the purity of `H_c^2` on a smooth affine
curve which need not be geometrically connected
(`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine`), after a
constant twist.

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two`: the top
  compactly supported cohomology of a pure lisse sheaf on a smooth affine curve has weights at
  most `w + 2`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

namespace WeilSheaf

/-- If `G` is a lisse Weil sheaf on a smooth affine curve `C₀`, punctually `ι`-pure of weight `v`,
and `b` is a unit with `|ι b| = q ^ (-v / 2)`, then `H_c^2(C, G)` is `ι`-pure of weight `v + 2`:
the constant twist `G ⊗ 𝓑_b` is punctually pure of weight `0`, so its `H_c^2` is pure of weight
`2` (`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine`, blueprint
`theorem-pure-lisse-sheaves-over-relative`), and it is `H_c^2(C, G)` with the Frobenius multiplied
by `b`.
-/
theorem isPureOfWeightOver_compactlySupportedCohomology_two_of_norm_eq
    (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l C) (hG : G.IsLisse) {v : ℝ}
    (hv : G.IsPunctuallyPureOfWeight ι v) {b : (PadicAlgCl l)ˣ}
    (hb : ‖ι b‖ = (Nat.card k₀ : ℝ) ^ (-v / 2)) :
    (G.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (v + 2) := by
  have h0 := isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine ι
    (G.constantTwist b) hG.constantTwist (hv.constantTwist_zero hb)
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_constantTwist G b 2
  have hq : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
  intro α hα
  have h1 := h0 (b * α) (e.symm.hasEigenvalue
    ((FrobeniusModule.hasEigenvalue_frobeniusEnd_rescale_iff b.ne_zero α).2 hα))
  rw [map_mul, norm_mul, hb] at h1
  calc ‖ι α‖ = ((Nat.card k₀ : ℝ) ^ (v / 2) * (Nat.card k₀ : ℝ) ^ (-v / 2)) * ‖ι α‖ := by
        rw [← Real.rpow_add hq, neg_div, add_neg_cancel, Real.rpow_zero, one_mul]
    _ = (Nat.card k₀ : ℝ) ^ (v / 2) * (Nat.card k₀ : ℝ) ^ ((2 : ℝ) / 2) := by
        rw [mul_assoc, h1]
    _ = (Nat.card k₀ : ℝ) ^ ((v + 2) / 2) := by
        rw [← Real.rpow_add hq, add_div]

end WeilSheaf

/-- *Top compact-support bound on a curve.* If `C₀` is a smooth affine curve and `G` is a lisse
Weil sheaf on `C₀`, punctually `ι`-pure of weight `w`, then `H_c^2(C, G)` has weights at most
`w + 2`.

The blueprint proof splits `C₀` into its connected components, and a connected component with
field of constants `k₁ = 𝔽_{q^d}` into the `d` geometrically connected curves over `k₁` which make
up its geometric fibre, permuted cyclically by the Frobenius. Weil sheaves over a finite extension
`k₁` of `k₀` are not available, so we use instead the purity of `H_c^2` of a sheaf punctually pure
of weight zero on a smooth affine curve, not necessarily geometrically connected (blueprint
`theorem-pure-lisse-sheaves-over-relative`), after a constant twist normalizing the weight to zero
(`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two_of_norm_eq`).
If `G` has no local Frobenius eigenvalue at all, it is punctually pure of the weights `0` and
`-2` at once, so `H_c^2(C, G)` is pure of the weights `2` and `0` at once and has no Frobenius
eigenvalue.
(blueprint: `lemma-degree-zero-top-cohomology--6`) -/
theorem WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two
    (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l C) (hG : G.IsLisse) {w : ℝ}
    (hw : G.IsPunctuallyPureOfWeight ι w) :
    (G.compactlySupportedCohomology 2).HasWeightsAtMostOver k₀ ι (w + 2) := by
  have hq : (1 : ℝ) < Nat.card k₀ := by exact_mod_cast Finite.one_lt_card
  by_cases hex : ∃ (x : C.finitePoints) (α : PadicAlgCl l),
      (G.stalk x).frobeniusEnd.HasEigenvalue α
  · obtain ⟨x, α, hα⟩ := hex
    obtain ⟨w', b, hw', hb⟩ := hw.exists_units_norm_eq ι
    -- the weight `w'` of the normalization is `w`, as seen on the eigenvalue `α`
    have hqx : (1 : ℝ) < (C ↘ Spec (CommRingCat.of k₀)).residueCard x.1 := by
      rw [Scheme.Hom.residueCard, Nat.cast_pow]
      exact one_lt_pow₀ hq (Scheme.Hom.degreeOver_ne_zero _ x.2)
    have hww' : w' / 2 = w / 2 :=
      (Real.rpow_right_inj (by linarith) hqx.ne').1 ((hw' x α hα).symm.trans (hw x α hα))
    obtain rfl : w' = w := by linarith
    exact (isPureOfWeightOver_compactlySupportedCohomology_two_of_norm_eq ι G hG hw'
      hb).hasWeightsAtMostOver
  · simp only [not_exists] at hex
    have hp (v : ℝ) : G.IsPunctuallyPureOfWeight ι v := fun x α hα ↦ (hex x α hα).elim
    have hq0 : (Nat.card k₀ : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h₂ := isPureOfWeightOver_compactlySupportedCohomology_two_of_norm_eq ι G hG (hp 0)
      (b := 1) (by simp)
    have h₀ := isPureOfWeightOver_compactlySupportedCohomology_two_of_norm_eq ι G hG (hp (-2))
      (b := Units.mk0 _ hq0) (by simp)
    intro α hα
    have h := (h₂ α hα).symm.trans (h₀ α hα)
    norm_num at h
    rw [h, Nat.cast_one] at hq
    exact (lt_irrefl _ hq).elim

end AlgebraicGeometry
