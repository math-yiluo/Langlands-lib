import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralStatements
import Langlands.Representation.Plancherel.ParabolicCharacterDecayProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalIwasawaCompactExistence

/-! # Structural choices for the conditional cuspidal finiteness reduction

The compact-open Iwasawa existence, finite central projection and level-preserving lifting
statements remain explicit premises. The other structural choices are supplied
by published results. This does not prove either unconditional finiteness target.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

/-- The structural-choice implication from the three remaining global inputs to
the exact fixed-coefficient finiteness target. -/
def RationalCuspidalCompactIwasawaFinitenessReductionStatement : Prop :=
  RationalIwasawaCompactExistenceStatement.{u} →
    RationalCuspidalCentralProjectionFiniteStatement.{u} →
    RationalCuspidalFixedCoefficientLiftingStatement.{u, uV} →
    RationalFixedCoefficientFinitenessStatement.{u, uV}

/-- Select the torus, chamber, compact open subgroup, positive-dimensional
closed representation and central Haar measure, then apply the published
fixed-span implication. All three remaining inputs are retained. -/
theorem rationalCuspidalCompactIwasawaFinitenessReduction :
    RationalCuspidalCompactIwasawaFinitenessReductionStatement.{u, uV} := by
  intro hIwasawa hfinite hlift F _ _ _ _ G _ _ hG T s hs
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let := hG.smooth
  let := hG.connectedSpace
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
  let : T2Space F := BruhatTits.localField_t2Space F
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : MeasurableSpace (rationalPoints G) := borel _
  let : BorelSpace (rationalPoints G) := ⟨rfl⟩
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  obtain ⟨S, i, ν, K, hi, hν, hKc, hPK⟩ := hIwasawa F G hG
  obtain ⟨N, ρ, hρ⟩ := exists_isClosedSubgroup_fin_succ G
  let : IsClosedImmersion s.hom.hom.left :=
    hs.isCentralSplitTorus.isSplitSubtorus.2
  let : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom s.hom.hom.left
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology F T.toGrp.X
  have hAc : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) :=
    (isClosedEmbedding_rationalPointMap F s.hom.hom).isClosed_range
  let : LocallyCompactSpace (rationalPoints.map s).range := hAc.locallyCompactSpace
  let muA : Measure (rationalPoints.map s).range := Measure.haar
  intro mu _ H hH χ hχ hu _
  have hunitary : IsUnitaryCharacter χ :=
    ⟨hu, (Units.continuous_val.comp hχ).measurable⟩
  exact hfinite.fixedCoefficientFiniteness hlift hG hi hν hKc hPK ρ hρ s hs
    muA mu χ hχ hunitary H hH

/-- The same three inputs also give the exact discrete-series twist-orbit
finiteness target through the published fixed-coefficient reduction. -/
theorem rationalDiscreteSeriesOrbitFiniteness_of_compactIwasawaCuspidalInputs
    (hIwasawa : RationalIwasawaCompactExistenceStatement.{u})
    (hfinite : RationalCuspidalCentralProjectionFiniteStatement.{u})
    (hlift : RationalCuspidalFixedCoefficientLiftingStatement.{u, uV}) :
    RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV} :=
  (rationalCuspidalCompactIwasawaFinitenessReduction hIwasawa hfinite hlift).orbitFiniteness

end Langlands.HarishChandraSchwartz
