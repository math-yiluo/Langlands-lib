import Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.CompleteProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothPointLifting
import Langlands.Global.CurvePlaceAdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Smooth point lifts over actual discrete completion integer rings -/

noncomputable section

universe u v w

open CategoryTheory
open _root_.AlgebraicGeometry IsDedekindDomain
open scoped Valued

namespace Langlands.Global

/-- A complete rank-one discrete valued field has a Henselian native
valuation subring, for the supplied valued uniformity. -/
theorem completeDiscreteValuationIntegers_henselian
    (K : Type u) [Field K] (Γ : Type v) [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [(Valued.v : Valuation K Γ).IsRankOneDiscrete] [CompleteSpace K] :
    HenselianLocalRing (Valued.v : Valuation K Γ).valuationSubring := by
  let R := (Valued.v : Valuation K Γ).valuationSubring
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete
  constructor
  intro f hf a₀ hroot hsimple
  exact HenselianRing.is_henselian f hf a₀ hroot
    (hsimple.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))

/-- The native integer ring of a height-one completion is Henselian. -/
theorem adicCompletionIntegers_henselian
    (A : Type w) [CommRing A] [IsDedekindDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (v : HeightOneSpectrum A) :
    HenselianLocalRing (v.adicCompletionIntegers K) :=
  completeDiscreteValuationIntegers_henselian (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))

/-- The native integer ring at an actual discrete curve place is Henselian. -/
theorem curvePlaceCompletionIntegers_henselian
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    (v : AlgebraicCurve.Place k F) :
    HenselianLocalRing (curvePlaceCompletionIntegers v) :=
  adicCompletionIntegers_henselian v.toValuationSubring F v.heightOneSpectrum

open Langlands.AlgebraicGeometry.PointTopology

/-- A chosen actual lift through a smooth map over a height-one completion
integer ring, preserving both the target and the supplied residue point. -/
def adicCompletionSmoothPointLift
    (C A K : Type u) [CommRing C] [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (v : HeightOneSpectrum A)
    [Algebra C (v.adicCompletionIntegers K)]
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y) [Smooth f.left]
    (p : RingPoint C Y (v.adicCompletionIntegers K))
    (q : RingPoint C X (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
    (hq : q ≫ f = RingPoint.changeRing
      (IsScalarTower.toAlgHom C (v.adicCompletionIntegers K)
        (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) p) :
    {a : RingPoint C X (v.adicCompletionIntegers K) //
      a ≫ f = p ∧ RingPoint.changeRing
        (IsScalarTower.toAlgHom C (v.adicCompletionIntegers K)
          (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) a = q} := by
  let : HenselianLocalRing (v.adicCompletionIntegers K) :=
    adicCompletionIntegers_henselian A K v
  exact henselianSmoothPointLift f
    (IsScalarTower.toAlgHom C (v.adicCompletionIntegers K)
      (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
    IsLocalRing.residue_surjective p q hq

/-- The same exact lift at any actual discrete curve place. -/
def curvePlaceCompletionSmoothPointLift
    (C : Type u) [CommRing C]
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    (v : AlgebraicCurve.Place k F) [Algebra C (curvePlaceCompletionIntegers v)]
    {X Y : Over (Spec (CommRingCat.of C))} (f : X ⟶ Y) [Smooth f.left]
    (p : RingPoint C Y (curvePlaceCompletionIntegers v))
    (q : RingPoint C X (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v)))
    (hq : q ≫ f = RingPoint.changeRing
      (IsScalarTower.toAlgHom C (curvePlaceCompletionIntegers v)
        (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v))) p) :
    {a : RingPoint C X (curvePlaceCompletionIntegers v) //
      a ≫ f = p ∧ RingPoint.changeRing
        (IsScalarTower.toAlgHom C (curvePlaceCompletionIntegers v)
          (IsLocalRing.ResidueField (curvePlaceCompletionIntegers v))) a = q} :=
  adicCompletionSmoothPointLift C v.toValuationSubring F v.heightOneSpectrum f p q hq

end Langlands.Global
