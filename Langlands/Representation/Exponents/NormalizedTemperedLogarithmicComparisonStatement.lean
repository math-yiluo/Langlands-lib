import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Plancherel.SplitTorusNormFormula

/-! # Corrected logarithmic comparison for normalized-exponent temperedness

This is a derived comparison consistent with the q^(-s) parameter in Renard
V.3.20. The paired Markdown distinguishes it from the printed raw-log formula
and retains the separate complex-exponential and structural obligations.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The corrected all-point logarithmic cone test, its negative-raw sign, and
the complete all-parabolic predicate comparison with nonempty presentations. -/
def NormalizedTemperedLogarithmicComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)]
      [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      (∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
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
              pres.nonnegCone))) ∧
      (IsNormalizedExponentTempered hG π ↔
        IsAdmissible π.representation ∧
          ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
            (A : CommGroupScheme (Spec (CommRingCat.of k)))
            (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
            (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
            (ha : IsSplitComponent a),
            Nonempty (ParabolicRootPresentation p l a) ∧
              ∀ (pres : ParabolicRootPresentation p l a)
                (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P)
                (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
                (hmul : IsIso (subgroupMultiplication l r))
                (χ : rationalPoints A.toGrp →* ℂˣ),
                IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
                  ∃ φ : RealTorusSpace.Vstar A, φ ∈ pres.nonnegCone ∧
                    ∀ t : rationalPoints A.toGrp,
                      Real.log ‖(χ t : ℂ)‖ =
                        (-Real.log (LocalField.residueCardinality k : ℝ)) *
                          RealTorusSpace.pair A φ
                            (Plancherel.SplitTorus.valuation
                              ha.isCentralSplitTorus.1.1 t).toAdd)

end Langlands.Aubert.General.RepresentedParabolic
