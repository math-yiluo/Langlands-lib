import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceStatements
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesCentralCoefficientSpace

/-! # Actual cuspidal central images: Waldspurger VIII.4 and the VIII.5 inclusion

These closed targets have no analytic convergence, finite-dimensionality or
decomposition premise. The level-preserving lifting target is separate from
the full-space equality. Only the elementary fixed-span implication is proved.
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

/-- Proposition VIII.4.1 for the actual raw image: it is exactly its complex
span, and that span is finite dimensional. Convergence is a separate closed target. -/
def RationalCuspidalCentralProjectionFiniteStatement : Prop :=
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
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G), IsSplitComponent s →
    ∀ (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
    ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
      (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup :
        Set (rationalPoints G → ℂ)) =
          rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup ∧
      FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup)

/-- Theorem VIII.4.2 as equality of the actual raw central-integral image and
the canonical algebraic discrete-series coefficient sum. The carrier universe
is enlarged to `max u uV` to accommodate actual function representations. -/
def RationalCuspidalDiscreteCoefficientStatement : Prop :=
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
        rationalCuspidalCentralImage hKc hPK ρ muA χ =
          (discreteSeriesCentralCoefficientSpace.{u, max u uV}
            (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
            mu χ : Set (rationalPoints G → ℂ))

/-- The level-preserving inclusion used in VIII.5. Each actual bi-invariant
coefficient has an actual cuspidal Schwartz preimage with the same level.
Full-space equality by itself is not a premise or a proof of this assertion. -/
def RationalCuspidalFixedCoefficientLiftingStatement : Prop :=
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
      ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
      ∀ ω ∈ discreteSeriesCentralFixed.{u, uV} (rationalPoints.map s).range
        hs.isCentralSplitTorus.isCentral.range_le_center mu χ H.toSubgroup,
      ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H.toSubgroup f →
        f ∈ rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup

section FixedSpan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}

/-- The elementary VIII.5 consequence for every displayed choice of the actual
Schwartz realization. It uses the published least fixed coefficient span. -/
theorem RationalCuspidalCentralProjectionFiniteStatement.fixedCoefficientFiniteness
    (hfinite : RationalCuspidalCentralProjectionFiniteStatement.{u})
    (hlift : RationalCuspidalFixedCoefficientLiftingStatement.{u, uV})
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
    ∀ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) →
      FiniteDimensional ℂ (discreteSeriesCentralFixedCoefficientSpace.{u, uV}
        (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
        mu χ H.toSubgroup) := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu H hH
  apply (finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_iff
    (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
    mu χ H.toSubgroup).mpr
  refine ⟨rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup,
    (hfinite F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχ hu H hH).2, ?_⟩
  intro ω hω f hf hHf
  exact Submodule.subset_span
    (hlift F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA mu χ hχ hu H hH ω hω f hf hHf)

end FixedSpan

end Langlands.HarishChandraSchwartz
