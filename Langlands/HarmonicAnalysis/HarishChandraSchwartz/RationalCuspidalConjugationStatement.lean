import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamber
import Langlands.Analysis.Local.QuotientMeasure

/-! # Exact actual-point targets for Waldspurger VIII.3.1 and VIII.3.2

These are proposition definitions, not proofs of the analytic conclusions.
Both conclusions include absolute convergence of every inner integral.
The quotient assertion is Bochner `Integrable`, including a.e. strong measurability.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.QuotientIntegration Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Conclusions

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The shared analytic convergence conclusion on the actual intrinsic kernel.
This proposition is not assumed in either closed statement below. -/
def RationalCuspidalConjugationConverges (muG : Measure (rationalPoints G)) : Prop :=
  ∀ f₁ : RationalSchwartzSpace hKc hPK ρ,
    f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ →
  ∀ (f₂ : RationalSchwartzSpace hKc hPK ρ) (h : rationalPoints G),
    Integrable (conjugationIntegrand (f₁ : rationalPoints G → ℂ)
      (f₂ : rationalPoints G → ℂ) h) muG

/-- The exact VIII.3.1 conclusion, with all inner integrals convergent and the
full ambient chamber intersected with actual `G¹`. -/
def RationalCuspidalConjugationBound (muG : Measure (rationalPoints G)) : Prop :=
  RationalCuspidalConjugationConverges hKc hPK ρ muG ∧
  ∀ f₁ : RationalSchwartzSpace hKc hPK ρ,
    f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ →
  ∀ (f₂ : RationalSchwartzSpace hKc hPK ρ) (r : ℝ),
    ∃ c : ℝ, 0 < c ∧ ∀ a : rationalMinimalChamberInNormKernel i ν,
      ‖rationalConjugationPairing hKc hPK ρ muG f₁ f₂ a‖ ≤
        c * (rationalMinimalModulus i ν (rationalMinimalChamberToParabolic i ν a) : ℝ≥0) *
          (1 + rationalHeight (F := F) ρ a) ^ (-r)

variable (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
  [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
  [BorelSpace (LeftQuotient (rationalPoints.map s).range)]

/-- The exact VIII.3.2 conclusion on the genuine split-central left quotient.
Its compatibility and Haar hypotheses appear in the closed statement below. -/
def RationalCuspidalConjugationIntegrability
    (muG : Measure (rationalPoints G))
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range)) : Prop :=
  RationalCuspidalConjugationConverges hKc hPK ρ muG ∧
  ∀ f₁ : RationalSchwartzSpace hKc hPK ρ,
    f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ →
  ∀ f₂ : RationalSchwartzSpace hKc hPK ρ,
    Integrable (rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂) muQ

variable [MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range)]
  [BorelSpace (rationalPoints G ⧸ (rationalPoints.map s).range)]

/-- The right-quotient formulation uses exactly the pushforward along the
published same-representative homeomorphism. -/
def RationalCuspidalRightConjugationIntegrability
    (muG : Measure (rationalPoints G))
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range)) : Prop :=
  letI := rationalSplitCenter_normal s hs
  RationalCuspidalConjugationConverges hKc hPK ρ muG ∧
  ∀ f₁ : RationalSchwartzSpace hKc hPK ρ,
    f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ →
  ∀ f₂ : RationalSchwartzSpace hKc hPK ρ,
    Integrable (rightConjugationPairing (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center muG
      (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ))
      (conjugationRightQuotientMeasure (rationalPoints.map s).range muQ)

/-- Elementary equivalence of the complete conclusions, retaining all-h inner
convergence and actual Bochner integrability on both quotient realizations. -/
theorem rationalCuspidalConjugationIntegrability_iff_right
    (muG : Measure (rationalPoints G))
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range)) :
    RationalCuspidalConjugationIntegrability hKc hPK ρ s hs muG muQ ↔
      RationalCuspidalRightConjugationIntegrability hKc hPK ρ s hs muG muQ := by
  let := rationalSplitCenter_normal s hs
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun f₁ hf₁ f₂ => ?_⟩
    exact (integrable_rightConjugationPairing_iff (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center muG
      (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ) muQ).mpr (h f₁ hf₁ f₂)
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun f₁ hf₁ f₂ => ?_⟩
    exact (integrable_rightConjugationPairing_iff (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center muG
      (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ) muQ).mp (h f₁ hf₁ f₂)

end Conclusions

/-- Closed actual-point Proposition VIII.3.1. The only additional external
structural input is Renard V.5.2's precisely named simultaneous basis property.
No decay, Xi estimate, convergence, summability or spectral input is a premise. -/
def RationalCuspidalConjugationBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G), SimultaneousStandardBasisAt i ν K0 →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ muG : Measure (rationalPoints G), muG.IsHaarMeasure →
      RationalCuspidalConjugationBound hKc hPK ρ muG

/-- Closed actual-point Corollary VIII.3.2, for explicit group and central Haar
measures and their compatible quotient measure with its displayed Borel structure.
Convergence and quotient measurability are conclusions. -/
def RationalCuspidalConjugationIntegrabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G), SimultaneousStandardBasisAt i ν K0 →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F)))
      (s : T.toGrp ⟶ G) (hs : IsSplitComponent s),
    ∀ [MeasurableSpace (rationalPoints.map s).range]
      [BorelSpace (rationalPoints.map s).range]
      [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
      [BorelSpace (LeftQuotient (rationalPoints.map s).range)]
      (muG : Measure (rationalPoints G)), muG.IsHaarMeasure →
    ∀ (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
      [muA.IsMulRightInvariant]
      (muQ : Measure (LeftQuotient (rationalPoints.map s).range)),
      IsCompatible (rationalPoints.map s).range muG muA muQ →
        RationalCuspidalConjugationIntegrability hKc hPK ρ s hs muG muQ

end Langlands.HarishChandraSchwartz
