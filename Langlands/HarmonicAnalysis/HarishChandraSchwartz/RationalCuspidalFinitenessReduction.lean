import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralStatements
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Plancherel.ParabolicCharacterDecayProof
import Langlands.BruhatTits.Iwasawa.ExistenceStatement

/-! # Structural choices for the conditional cuspidal finiteness reduction

The Iwasawa existence, finite central projection and level-preserving lifting
statements remain explicit premises. The other structural choices are supplied
by published results. This does not prove either unconditional finiteness target.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

/-- The structural-choice implication from the three remaining global inputs to
the exact fixed-coefficient finiteness target. -/
def RationalCuspidalFinitenessReductionStatement : Prop :=
  BruhatTits.Iwasawa.IwasawaExistenceStatement.{u} →
    RationalCuspidalCentralProjectionFiniteStatement.{u} →
    RationalCuspidalFixedCoefficientLiftingStatement.{u, uV} →
    RationalFixedCoefficientFinitenessStatement.{u, uV}

/-- Select the torus, chamber, compact open subgroup, positive-dimensional
closed representation and central Haar measure, then apply the published
fixed-span implication. All three remaining inputs are retained. -/
theorem rationalCuspidalFinitenessReduction :
    RationalCuspidalFinitenessReductionStatement.{u, uV} := by
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
  obtain ⟨S, i, ν, hi, hν⟩ :=
    RationalPointFamily.exists_maximalSplitTorus_genericCocharacter hG
  have := hi.isSplitSubtorus.mono
  obtain ⟨_, D, _, _, _, _, x, _, hprops, _, hproducts, _⟩ :=
    hIwasawa F G hG S i hi ν hν
  let K : OpenSubgroup (rationalPoints G) :=
    ⟨D.specialCompactSubgroup x, hprops.2.1.2.1⟩
  have hKc : IsCompact (K : Set (rationalPoints G)) := hprops.2.1.1
  have hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup :=
    isIwasawaPair_of_pointProductEqualities (hproducts.2.2.1 ∅ (Set.empty_subset _))
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
theorem rationalDiscreteSeriesOrbitFiniteness_of_cuspidalInputs
    (hIwasawa : BruhatTits.Iwasawa.IwasawaExistenceStatement.{u})
    (hfinite : RationalCuspidalCentralProjectionFiniteStatement.{u})
    (hlift : RationalCuspidalFixedCoefficientLiftingStatement.{u, uV}) :
    RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV} :=
  (rationalCuspidalFinitenessReduction hIwasawa hfinite hlift).orbitFiniteness

end Langlands.HarishChandraSchwartz
