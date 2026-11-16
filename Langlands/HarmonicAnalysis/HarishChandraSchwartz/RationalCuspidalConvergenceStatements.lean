import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralImage

/-! # Closed convergence and vanishing comparison targets for actual Schwartz functions

The estimates needed for these targets are conclusions to be proved, not premises.
The standard constant-term condition ranges over every proper root subset and all
two-sided translates. Comparison with the full semistandard index is separate.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- Absolute convergence of the actual central integral for every Schwartz function.
All torus, chamber, compact subgroup and height choices are visible. -/
def RationalSchwartzCentralConvergenceStatement : Prop :=
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
      CentralIntegralConvergesOn (⊤ : Submodule ℂ (RationalSchwartzSpace hKc hPK ρ)) muA χ

/-- Convergence of the actual radical integrals for all Schwartz functions, proper
standard root subsets, Haar measures and translates, with no estimate premise. -/
def RationalSchwartzConstantTermConvergenceStatement : Prop :=
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
    ∀ (f : RationalSchwartzSpace hKc hPK ρ)
      (I : Finset (RationalPointFamily.SimpleRoot i ν)),
      RationalPointFamily.rootSet i ν I ≠ simpleRelativeRoots i ν →
    ∀ (muU : Measure (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)))
      [muU.IsHaarMeasure] (x y : rationalPoints G),
      Integrable (fun v : standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I) =>
        f (x * (v : rationalPoints G) * y)) muU

section Vanishing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

/-- The vanishing-only all-standard formulation. Its integral is the published
normalized induced constant term on the actual radical and actual Levi. -/
def RationalStandardConstantTermsVanish (f : rationalPoints G → ℂ) : Prop :=
  ∀ I : Finset (RationalPointFamily.SimpleRoot i ν),
    RationalPointFamily.rootSet i ν I ≠ simpleRelativeRoots i ν →
  ∀ muU : Measure (standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)),
    muU.IsHaarMeasure → ∀ g : rationalPoints G × rationalPoints G,
      constantTermInd muU (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
        f g = 0

end Vanishing

/-- The convergence-strengthened kernel equals normalized constant-term vanishing
alone, for every actual Schwartz function. No convergence is assumed here. -/
def RationalCuspidalVanishingComparisonStatement : Prop :=
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
    ∀ f : RationalSchwartzSpace hKc hPK ρ,
      f ∈ rationalCuspidalSubmodule hKc hPK ρ ↔
        RationalStandardConstantTermsVanish (i := i) (ν := ν) f

/-- Closed constant-term convergence implies exactly the closed vanishing comparison. -/
theorem RationalSchwartzConstantTermConvergenceStatement.vanishingComparison
    (h : RationalSchwartzConstantTermConvergenceStatement.{u}) :
    RationalCuspidalVanishingComparisonStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ f
  rw [mem_rationalCuspidalSubmodule_iff_constantTermInd]
  constructor
  · intro hf I hI muU hmuU
    exact (hf I hI muU hmuU).2
  · intro hf I hI muU hmuU
    let := hmuU
    exact ⟨fun x y => h F G hG S i hi ν hν K hKc hPK N ρ hρ f I hI muU x y,
      hf I hI muU hmuU⟩

end Langlands.HarishChandraSchwartz
