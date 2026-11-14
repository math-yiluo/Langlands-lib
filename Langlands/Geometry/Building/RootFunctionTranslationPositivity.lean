import Langlands.Geometry.Building.ReflectionRealizationUniqueness
import Mathlib.Topology.Algebra.Order.Field

/-! # Strict positivity from nonnegative nearby torus translations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace RootFunctionFamily

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A root value stays nonnegative near zero on every real line of torus
translations. The neighbourhood may depend on the translation direction. -/
def NonnegativeNearTranslations (φ : RootFunctionFamily S G)
    (a : characterLattice S) (g : rationalPoints G) : Prop :=
  ∀ v : V S, ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ (t • v +ᵥ φ) a g

/-- For a nonzero character of a split torus, strict positivity is equivalent
to nonnegativity near zero along every real translation line. This applies to
arbitrary root-function families, without any root-valuation axiom. -/
theorem strictPositive_iff_nonnegativeNearTranslations
    (hS : IsSplitTorus S.toGrp) (φ : RootFunctionFamily S G)
    {a : characterLattice S} (ha : a ≠ 0) (g : rationalPoints G) :
    0 < φ a g ↔ φ.NonnegativeNearTranslations a g := by
  induction hq : φ a g using WithTop.recTopCoe with
  | top =>
    simp only [hq, NonnegativeNearTranslations, vadd_apply, WithTop.top_add]
    exact ⟨fun _ _ => Filter.Eventually.of_forall fun _ => le_top,
      fun _ => WithTop.coe_lt_top 0⟩
  | coe q =>
    constructor
    · intro hpos v
      have hqpos : 0 < q := WithTop.coe_lt_coe.mp (hq ▸ hpos)
      have hlim : Tendsto (fun t : ℝ => q + t * eval S a v) (𝓝 0) (𝓝 q) := by
        have hc : Continuous (fun t : ℝ => q + t * eval S a v) := by fun_prop
        simpa only [zero_mul, add_zero] using hc.tendsto 0
      filter_upwards [hlim.eventually (eventually_gt_nhds hqpos)] with t ht
      simpa only [vadd_apply, hq, map_smul, smul_eq_mul, ← WithTop.coe_add,
        ← WithTop.coe_zero, WithTop.coe_le_coe] using ht.le
    · intro hnear
      have hzero := (hnear 0).self_of_nhds
      have hqnonneg : 0 ≤ q := by
        simpa only [zero_smul, zero_vadd, hq, ← WithTop.coe_zero,
          WithTop.coe_le_coe] using hzero
      have hqne : q ≠ 0 := by
        intro hqzero
        obtain ⟨v, hv⟩ := exists_eval_ne_zero hS ha
        let w : V S := (-(eval S a v)⁻¹) • v
        have hw : eval S a w = -1 := by
          simp only [w, map_smul, smul_eq_mul, neg_mul, inv_mul_cancel₀ hv]
        obtain ⟨l, r, hbounds, hsub⟩ := (hnear w).exists_Ioo_subset
        have ht := hsub (show r / 2 ∈ Set.Ioo l r from ⟨by linarith [hbounds.1, hbounds.2],
          by linarith [hbounds.2]⟩)
        change 0 ≤ ((r / 2) • w +ᵥ φ) a g at ht
        have hbad : 0 ≤ -(r / 2) := by
          have ht' : (0 : WithTop ℝ) ≤ ↑(-(r / 2)) := by
            simpa only [vadd_apply, hq, hqzero, map_smul, smul_eq_mul, hw,
              mul_neg_one, WithTop.coe_zero, zero_add] using ht
          exact WithTop.coe_le_coe.mp ht'
        linarith [hbounds.2]
      rw [← WithTop.coe_zero, WithTop.coe_lt_coe]
      exact lt_of_le_of_ne hqnonneg (Ne.symm hqne)

/-- A value-zero root cannot stay nonnegative on a neighbourhood along every
torus translation line. -/
theorem not_nonnegativeNearTranslations_of_eq_zero
    (hS : IsSplitTorus S.toGrp) (φ : RootFunctionFamily S G)
    {a : characterLattice S} (ha : a ≠ 0) (g : rationalPoints G)
    (hzero : φ a g = 0) : ¬ φ.NonnegativeNearTranslations a g := by
  rw [← strictPositive_iff_nonnegativeNearTranslations hS φ ha g, hzero]
  exact lt_irrefl _

end RootFunctionFamily

end Langlands.Geometry.Building
