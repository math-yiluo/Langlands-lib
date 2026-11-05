import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnramifiedCharacterExtension
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientGeneration
import Langlands.Representation.Plancherel.RationalTwistStabilizer

/-! # Finiteness of `Θ^H_G` for the rational points of a connected reductive group

Waldspurger, VIII.5 (printed pp. 331–332), proof of Theorem VIII.1.2, for the actual group
`G(F)` of a connected reductive group over a nonarchimedean local field, with `A_G` the image of
a split component and `G¹` the common kernel of the absolute values of the rational characters.
The hypotheses `H ≤ G¹` and "`A_G ∩ G¹` compact" of the abstract reduction are discharged here;
the remaining input is the finite-dimensional space `p_χ(°C_H)` of Proposition VIII.4.1 and
Theorem VIII.4.2.

* `rationalDiscreteSeriesFixedOrbits`: Waldspurger's `Θ^H_G` for `G(F)` and a central `A`;
* `isClosed_range_splitComponent`: the image of a split component in `G(F)` is closed;
* `finite_rationalDiscreteSeriesFixedOrbits_of_finite_central` and
  `finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional`: the two finiteness theorems.
-/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance instRationalDiscreteSeriesOrbitFiniteness1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalDiscreteSeriesOrbitFiniteness2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
variable (s : T.toGrp ⟶ G)

omit [LocallyOfFiniteType G.X.hom] in
/-- The image `A_G(F)` of a split component in `G(F)` is closed: the split component is a
closed immersion, and rational points of a closed immersion form a closed embedding
(`isClosedEmbedding_rationalPointMap`). -/
theorem isClosed_range_splitComponent (hs : GroupScheme.IsSplitComponent s) :
    IsClosed ((GroupScheme.rationalPoints.map s).range : Set (GroupScheme.rationalPoints G)) := by
  have : IsClosedImmersion s.hom.hom.left := hs.isCentralSplitTorus.isSplitSubtorus.2
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom s.hom.hom.left
  have : T2Space F := BruhatTits.localField_t2Space F
  let : TopologicalSpace (RationalPoint F T.toGrp.X) := rationalPointTopology F T.toGrp.X
  have hce : Topology.IsClosedEmbedding (fun p : RationalPoint F T.toGrp.X => p ≫ s.hom.hom) :=
    isClosedEmbedding_rationalPointMap F s.hom.hom
  rw [MonoidHom.coe_range]
  exact hce.isClosed_range

omit [LocallyOfFiniteType G.X.hom] in
/-- `A_G(F) ∩ G¹` is compact for a split component (`isCompact_rationalNormKernelPart`). -/
theorem isCompact_splitComponent_inf_commonNormKernel (hG : GroupScheme.IsConnectedReductive G)
    (hs : GroupScheme.IsSplitComponent s) :
    IsCompact (((GroupScheme.rationalPoints.map s).range ⊓
      commonNormKernel (fun psi => (rationalNormCharacters G psi).toMul) :
        Subgroup (GroupScheme.rationalPoints G)) : Set (GroupScheme.rationalPoints G)) :=
  isCompact_rationalNormKernelPart G hG _ hs.isCentralSplitTorus.isCentral.range_le_center
    (isClosed_range_splitComponent G s hs)

variable [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
variable (mu : MeasureTheory.Measure
  (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))

/-- **Waldspurger's `Θ^H_G` for `G(F)`** (VIII.1, printed p. 321): the twist orbits, under
the actual unitary unramified characters, of discrete-series classes of `G(F)` modulo the
central subgroup `(rationalPoints.map s).range` that have a nonzero `H`-fixed vector. -/
def rationalDiscreteSeriesFixedOrbits (hs : GroupScheme.IsCentral s) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu], Subgroup (GroupScheme.rationalPoints G) →
      Set (DiscreteSeriesOrbitClass.{u, u, uV} (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul)) := by
  letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ H
  exact discreteSeriesFixedOrbits.{u, uV} _ hs.range_le_center mu _ H

/-- **Theorem VIII.1.2 for `G(F)` from the finiteness of the `E₂(G)^H_χ`** (Waldspurger,
VIII.5, printed pp. 331–332). Let `G` be connected reductive, `A_G(F)` the image of a split
component and `H` a compact open subgroup of `G(F)`. If `E₂(G)^H_χ` is finite for every
continuous unitary character `χ` of `A_G(F)` trivial on `A_G(F) ∩ H`, then `Θ^H_G` is
finite. -/
theorem finite_rationalDiscreteSeriesFixedOrbits_of_finite_central
    (hG : GroupScheme.IsConnectedReductive G) (hs : GroupScheme.IsSplitComponent s) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu] (H : Subgroup (GroupScheme.rationalPoints G)),
      IsOpen (H : Set (GroupScheme.rationalPoints G)) →
      IsCompact (H : Set (GroupScheme.rationalPoints G)) →
      (∀ χ : (GroupScheme.rationalPoints.map s).range →* ℂˣ, Continuous χ →
        (∀ a, ‖(χ a : ℂ)‖ = 1) →
        (∀ a : (GroupScheme.rationalPoints.map s).range,
          (a : GroupScheme.rationalPoints G) ∈ H → χ a = 1) →
        (discreteSeriesCentralFixed.{u, uV} _ hs.isCentralSplitTorus.isCentral.range_le_center
          mu χ H).Finite) →
      (rationalDiscreteSeriesFixedOrbits.{u, uV} G s mu hs.isCentralSplitTorus.isCentral H).Finite := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  intro _ H hHo hHc hfin
  exact finite_discreteSeriesFixedOrbits_of_finite_central _ _ mu _ H hHo
    (compactSubgroup_le_rationalCommonNormKernel G H hHc)
    (isCompact_splitComponent_inf_commonNormKernel G s hG hs) hfin

/-- **Theorem VIII.1.2 for `G(F)` from Proposition VIII.4.1 and Theorem VIII.4.2** (Waldspurger,
VIII.5, printed pp. 331–332). Let `G` be connected reductive, `A_G(F)` the image of a split
component and `H` a compact open subgroup of `G(F)`. If for every continuous unitary character
`χ` of `A_G(F)` trivial on `A_G(F) ∩ H` the `H`-bi-invariant coefficients of all
`ω ∈ E₂(G)^H_χ` lie in one finite-dimensional space (Waldspurger's `p_χ(°C_H)`), then `Θ^H_G`
is finite. -/
theorem finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional
    (hG : GroupScheme.IsConnectedReductive G) (hs : GroupScheme.IsSplitComponent s) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    ∀ [MeasureTheory.Measure.IsHaarMeasure mu] (H : OpenSubgroup (GroupScheme.rationalPoints G)),
      IsCompact (H : Set (GroupScheme.rationalPoints G)) →
      (∀ χ : (GroupScheme.rationalPoints.map s).range →* ℂˣ, Continuous χ →
        (∀ a, ‖(χ a : ℂ)‖ = 1) →
        (∀ a : (GroupScheme.rationalPoints.map s).range,
          (a : GroupScheme.rationalPoints G) ∈ H → χ a = 1) →
        ∃ E : Submodule ℂ (GroupScheme.rationalPoints G → ℂ), FiniteDimensional ℂ E ∧
          ∀ ω ∈ discreteSeriesCentralFixed.{u, uV} _
              hs.isCentralSplitTorus.isCentral.range_le_center mu χ H.toSubgroup,
            ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H.toSubgroup f →
              f ∈ E) →
      (rationalDiscreteSeriesFixedOrbits.{u, uV} G s mu hs.isCentralSplitTorus.isCentral
        H.toSubgroup).Finite := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  intro _ H hH hF
  exact finite_discreteSeriesFixedOrbits_of_finiteDimensional _ _ mu _ H hH
    (compactSubgroup_le_rationalCommonNormKernel G H.toSubgroup hH)
    (isCompact_splitComponent_inf_commonNormKernel G s hG hs) hF

end Langlands.HarishChandraSchwartz
