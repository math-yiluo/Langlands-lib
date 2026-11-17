import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralStatements

/-! # The lower inclusion of Waldspurger VIII.4.2 at an independent carrier universe

The first half of the proof of Theorem VIII.4.2 shows `A₂(G)_χ ⊆ p_χ(°C(G))`.
This module states that inclusion as a closed proposition on the actual interfaces,
with the carrier universe `uV` independent of the field universe. It is not proved here.
Two elementary consequences are proved: its instance at `max u uV` is one half of the
published equality target, and it places each coefficient of a class in
`discreteSeriesCentralFixed` in the full raw image.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The inclusion `A₂(G)_χ ⊆ p_χ(°C(G))` of Theorem VIII.4.2 for the actual raw
central-integral image of the actual cuspidal Schwartz space and the canonical
algebraic sum of discrete-series coefficient spaces in carrier universe `uV`. -/
def RationalCuspidalDiscreteCoefficientLowerInclusionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s)
      (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure],
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
        (discreteSeriesCentralCoefficientSpace.{u, uV}
            (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
            mu χ : Set (rationalPoints G → ℂ)) ⊆
          rationalCuspidalCentralImage hKc hPK ρ muA χ

/-- At carrier universe `max u uV` the lower inclusion is the inclusion `⊇` of the
published equality target, stated for the same structural choices. -/
theorem RationalCuspidalDiscreteCoefficientLowerInclusionStatement.supset
    (hlower : RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, max u uV}) :
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
        IsMaximalSplitTorus i →
      ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
      ∀ (K : OpenSubgroup (rationalPoints G))
        (hKc : IsCompact (K : Set (rationalPoints G)))
        (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
        (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
        (hs : IsSplitComponent s)
        (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure],
        letI := (rationalPoints.map s).range.normal_of_le_center
          hs.isCentralSplitTorus.isCentral.range_le_center
        letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
        ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
          (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
          (discreteSeriesCentralCoefficientSpace.{u, max u uV}
              (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
              mu χ : Set (rationalPoints G → ℂ)) ⊆
            rationalCuspidalCentralImage hKc hPK ρ muA χ :=
  hlower

section Fixed

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}

/-- Each coefficient of the canonical representative of a class in
`discreteSeriesCentralFixed` lies in the full raw central image. -/
theorem RationalCuspidalDiscreteCoefficientLowerInclusionStatement.coefficient_mem
    (hlower : RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u, uV})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ) (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure] :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
    ∀ H : Subgroup (rationalPoints G),
    ∀ ω ∈ discreteSeriesCentralFixed.{u, uV} (rationalPoints.map s).range
        hs.isCentralSplitTorus.isCentral.range_le_center mu χ H,
    ∀ f ∈ coefficientFunctionSpace ω.val.out.obj,
      f ∈ rationalCuspidalCentralImage hKc hPK ρ muA χ := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu H ω hω f hf
  exact hlower F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA mu χ hχ hu
    (coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace
      (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
      mu χ ω hω.1 hf)

end Fixed

end Langlands.HarishChandraSchwartz
