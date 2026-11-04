import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure

/-! # Upper Haar volumes of actual rational lattice cells modulo the full center -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal ENNReal BigOperators

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

/-- A supplied simultaneous standard basis bounds the actual full-center
quotient cells by the product of the individual standard-parabolic ray weights.
No volume estimate or index identity is supplied as a premise. -/
def RationalLatticeQuotientVolumeStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)]
      [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (_hν : IsGenericCocharacter i ν)
      (_hStandard : StandardCocharacterStatement.{u})
      (hU : ∀ J : Finset (SimpleRoot i ν),
        IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
      (K0 : Subgroup (RationalPoint k G.X)),
      SimultaneousStandardBasisAt i ν K0 →
      ∀ (I : Type w) [Fintype I] [DecidableEq I]
        (J : I → Finset (SimpleRoot i ν)) (x : I → cocharacterLattice T),
        (∀ a β, β ∈ J a → simpleRootPairing i ν β (x a) = 0) →
        (∀ a β, β ∉ J a → 0 ≤ simpleRootPairing i ν β (x a)) →
        ∀ z : ∀ a, Subgroup.center (levi i ν (J a)),
          (∀ a, ((z a : levi i ν (J a)) : RationalPoint k G.X) =
            uniformizerPowers i (.ofAdd (x a))) →
          ∀ (K : OpenSubgroup (RationalPoint k G.X)),
            IsCompact (K : Set (RationalPoint k G.X)) →
            ∀ (F₀ : Set (RationalPoint k G.X)), F₀.Finite →
              ∀ [MeasurableSpace
                  (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X))]
                [BorelSpace
                  (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X))]
                (measure : MeasureTheory.Measure
                  (RationalPoint k G.X ⧸ Subgroup.center (RationalPoint k G.X)))
                [MeasureTheory.Measure.IsHaarMeasure measure],
                ∃ D : ℝ, 0 < D ∧
                  ∀ (n : I → ℕ) (t : RationalPoint k G.X), t ∈ F₀ →
                    let cell :=
                      (QuotientGroup.mk :
                        RationalPoint k G.X →
                          RationalPoint k G.X ⧸
                            Subgroup.center (RationalPoint k G.X)) ''
                        DoubleCoset.doubleCoset
                          (uniformizerPowers i (.ofAdd (∑ a, n a • x a)) * t)
                          K.toSubgroup K.toSubgroup
                    MeasurableSet cell ∧
                      measure cell ≤ ENNReal.ofReal (D * ∏ a,
                        (((HaarModulus.closedRestrictCharacter (unipotent i ν (J a))
                          (hU (J a)) (levi i ν (J a)) (levi_le_normalizer i ν (J a))
                          (z a : levi i ν (J a)) : ℝ≥0) : ℝ))⁻¹ ^ n a)

end Langlands.Aubert.General.RationalPointFamily
