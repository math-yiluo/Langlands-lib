import Langlands.Representation.Exponents.NormalizedTemperedLogarithmicComparisonStatement

/-! # Corrected logarithmic comparison for normalized-exponent temperedness -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

set_option maxHeartbeats 800000 in
/-- The explicit logarithmic test retains the normalized parameter's root cone
and all actual parabolic and presentation quantifiers. -/
theorem normalizedTemperedLogarithmicComparison :
    NormalizedTemperedLogarithmicComparisonStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π
  have localComparison :
      ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
        (A : CommGroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (ha : IsSplitComponent a)
        (pres : ParabolicRootPresentation p l a)
        (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r))
        (χ : rationalPoints A.toGrp →* ℂˣ),
        IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
          ((Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
              pres.nonnegCone ↔
            ∃ φ : RealTorusSpace.Vstar A, φ ∈ pres.nonnegCone ∧
              ∀ t : rationalPoints A.toGrp,
                Real.log ‖(χ t : ℂ)‖ =
                  (-Real.log (LocalField.residueCardinality k : ℝ)) *
                    RealTorusSpace.pair A φ
                      (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd) ∧
           (Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
              pres.nonnegCone ↔
            (-Plancherel.SplitTorus.rawLogRealPart ha.isCentralSplitTorus.1.1 χ) ∈
              pres.nonnegCone)) := by
    intro P M A p l a hp hl ha pres U r hr hmul χ hχ
    have := ha.isAffine
    let := RationalPointFamily.splitComponentPointTopology ha
    have hopen := (isNormalizedJacquetExponent_iff_isOpen_ker_and
      p l r hp hl hr hmul ha π χ).mp hχ |>.1
    have hq : 0 < Real.log (LocalField.residueCardinality k : ℝ) :=
      Real.log_pos (by exact_mod_cast LocalField.residueCardinality_gt_one k)
    have hneg : -Real.log (LocalField.residueCardinality k : ℝ) ≠ 0 :=
      neg_ne_zero.mpr hq.ne'
    have hlog (t : rationalPoints A.toGrp) :
        Real.log ‖(χ t : ℂ)‖ =
          (-Real.log (LocalField.residueCardinality k : ℝ)) *
            RealTorusSpace.pair A
              (Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ)
              (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd := by
      calc
        Real.log ‖(χ t : ℂ)‖ =
            RealTorusSpace.pair A
              (Plancherel.SplitTorus.rawLogRealPart ha.isCentralSplitTorus.1.1 χ)
              (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd :=
          (Plancherel.SplitTorus.pair_rawLogRealPart_valuation
            ha.isCentralSplitTorus.1.1 χ hopen t).symm
        _ = _ := by
          rw [Plancherel.SplitTorus.rawLogRealPart, map_smul, LinearMap.smul_apply]
          rfl
    constructor
    · constructor
      · intro hm
        exact ⟨Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ,
          hm, hlog⟩
      · rintro ⟨φ, hφ, hφlog⟩
        have heq :
            Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = φ := by
          apply Plancherel.SplitTorus.eq_of_pair_valuation_eq ha.isCentralSplitTorus.1.1
          intro t
          apply mul_left_cancel₀ hneg
          exact (hlog t).symm.trans (hφlog t)
        rw [heq]
        exact hφ
    · have hsign :
          -Plancherel.SplitTorus.rawLogRealPart ha.isCentralSplitTorus.1.1 χ =
            Real.log (LocalField.residueCardinality k : ℝ) •
              Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ := by
        rw [Plancherel.SplitTorus.rawLogRealPart, neg_smul, neg_neg]
      rw [hsign]
      constructor
      · exact pres.smul_mem_nonnegCone hq.le
      · intro hm
        have hi := pres.smul_mem_nonnegCone (inv_nonneg.mpr hq.le) hm
        simpa only [smul_smul, inv_mul_cancel₀ hq.ne', one_smul] using hi
  refine ⟨localComparison, ?_⟩
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro P M A p l a hp hl ha
    have hc := h.parabolic p l a hp hl ha
    refine ⟨hc.1, ?_⟩
    intro pres U r hr hmul χ hχ
    exact (localComparison P M A p l a hp hl ha pres U r hr hmul χ hχ).1.mp
      (hc.2 pres U r hr hmul χ hχ)
  · rintro ⟨hadm, h⟩
    refine ⟨hadm, ?_⟩
    intro P M A p l a hp hl ha
    have hc := h P M A p l a hp hl ha
    refine ⟨hc.1, ?_⟩
    intro pres U r hr hmul χ hχ
    exact (localComparison P M A p l a hp hl ha pres U r hr hmul χ hχ).1.mpr
      (hc.2 pres U r hr hmul χ hχ)

end Langlands.Aubert.General.RepresentedParabolic
