import Langlands.AlgebraicGeometry.PointTopology.ValuedAlgebraicExtension
import Langlands.FieldTheory.HenselianSeparableIntegerAddValuation

/-! # Cofinal bounds over separable extensions of henselian discretely valued fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry ValuativeRel

namespace Langlands.AlgebraicGeometry.PointTopology

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] [ValuativeRel k]
  (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible]
  (hH : HenselianLocalRing v.valuationSubring)

/-- The chosen normalized additive extension induces the original valuative
relation on embedded base elements. -/
theorem henselianSeparableAddValuation_base_le_iff (a b : k) :
    FieldTheory.henselianSeparableAddValuation v hH K (algebraMap k K b) ≤
        FieldTheory.henselianSeparableAddValuation v hH K (algebraMap k K a) ↔
      a ≤ᵥ b := by
  by_cases ha : a = 0
  · subst a
    simp [zero_vle]
  by_cases hb : b = 0
  · subst b
    simp [vle_zero_iff, ha]
  rw [FieldTheory.henselianSeparableAddValuation_base v hH K hb,
    FieldTheory.henselianSeparableAddValuation_base v hH K ha,
    WithTop.coe_le_coe, Int.cast_le, neg_le_neg_iff,
    WithZero.log_le_iff_le_exp (v.ne_zero_iff.mpr ha),
    WithZero.exp_log (v.ne_zero_iff.mpr hb), v.vle_iff_le]

/-- A separable extension of the henselian discretely valued base carries a
compatible relation in which every extension bound is dominated by a nonzero
base element. No completeness or residue-field assumption is needed. -/
def henselianSeparableCofinalValuativeExtension
    (hv : Function.Surjective v) : CofinalValuativeExtension k K := by
  let w := FieldTheory.henselianSeparableAddValuation v hH K
  letI : ValuativeRel K := ValuativeRel.ofValuation w.toValuation
  refine ⟨inferInstance, ⟨fun a b => ?_⟩, ?_⟩
  · change w (algebraMap k K b) ≤ w (algebraMap k K a) ↔ a ≤ᵥ b
    exact henselianSeparableAddValuation_base_le_iff v hH a b
  · intro c
    by_cases hc : c = 0
    · exact ⟨1, one_ne_zero, hc ▸ zero_vle _⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (w.ne_top_iff.mpr hc)
    obtain ⟨n, hn⟩ := exists_int_le r
    obtain ⟨b, hb⟩ := hv (WithZero.exp (-n))
    have hb0 : b ≠ 0 := by
      intro h
      rw [h, map_zero] at hb
      exact WithZero.zero_ne_coe hb
    refine ⟨b, hb0, ?_⟩
    change w (algebraMap k K b) ≤ w c
    rw [FieldTheory.henselianSeparableAddValuation_base v hH K hb0,
      hb, WithZero.log_exp, neg_neg, ← hr, WithTop.coe_le_coe]
    exact hn

/-- Under the constructed extension relation, the prescribed inequality is
exactly the reversed normalized additive-value inequality. -/
theorem henselianSeparableCofinalValuativeExtension_vle_iff
    (hv : Function.Surjective v) (a b : K) :
    letI := (henselianSeparableCofinalValuativeExtension v hH hv (K := K)).relation
    a ≤ᵥ b ↔
      FieldTheory.henselianSeparableAddValuation v hH K b ≤
        FieldTheory.henselianSeparableAddValuation v hH K a := Iff.rfl

/-- Actual regular-function bounds descend from the chosen separable extension
without a local-field hypothesis on the base. -/
theorem isAlgebraicallyBounded_of_henselianSeparableExtension
    (hv : Function.Surjective v)
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    (B : Set (RationalPoint k X))
    (hB : letI :=
      (henselianSeparableCofinalValuativeExtension v hH hv (K := K)).relation
      IsAlgebraicallyBounded K (ringBaseChange k K X)
        (geometricRationalPoint (K := K) X '' B)) :
    IsAlgebraicallyBounded k X B := by
  let e := henselianSeparableCofinalValuativeExtension v hH hv (K := K)
  let := e.relation
  let := e.extension
  exact isAlgebraicallyBounded_of_geometricRationalPoint X e.cofinal B hB

end Langlands.AlgebraicGeometry.PointTopology
