import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFinitenessStatement

/-! # The remaining fixed-coefficient finiteness target in Waldspurger VIII.5

The span below is constructed from the actual coefficient spaces, with a fixed central
character and compact-open level. Its finite dimensionality is an analytic obligation,
motivated by VIII.4.1 and VIII.4.2, and implies the existing VIII.1.2 target.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

universe u uG uV

section Coefficients

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] (mu : Measure (G ⧸ A)) [mu.IsHaarMeasure]
  (χ : A →* ℂˣ) (H : Subgroup G)

/-- The span of the `H`-bi-invariant coefficient functions of the discrete-series classes
with central character `χ` and nonzero `H` invariants. Representatives are the same
`Quotient.out` representatives used by the published VIII.5 finiteness reduction. -/
def discreteSeriesCentralFixedCoefficientSpace : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {f | ∃ ω ∈ discreteSeriesCentralFixed.{uG, uV} A hA mu χ H,
    f ∈ coefficientFunctionSpace ω.val.out.obj ∧ IsBiInvariant H f}

theorem mem_discreteSeriesCentralFixedCoefficientSpace
    {ω : DiscreteSeriesClass.{uG, uV} A hA mu}
    (hω : ω ∈ discreteSeriesCentralFixed A hA mu χ H) {f : G → ℂ}
    (hf : f ∈ coefficientFunctionSpace ω.val.out.obj) (hH : IsBiInvariant H f) :
    f ∈ discreteSeriesCentralFixedCoefficientSpace.{uG, uV} A hA mu χ H :=
  Submodule.subset_span ⟨ω, hω, hf, hH⟩

/-- A submodule contains this span exactly when it contains all the defining coefficients. -/
theorem discreteSeriesCentralFixedCoefficientSpace_le_iff (E : Submodule ℂ (G → ℂ)) :
    discreteSeriesCentralFixedCoefficientSpace.{uG, uV} A hA mu χ H ≤ E ↔
      ∀ ω ∈ discreteSeriesCentralFixed.{uG, uV} A hA mu χ H,
        ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H f → f ∈ E := by
  constructor
  · intro hE ω hω f hf hH
    exact hE (mem_discreteSeriesCentralFixedCoefficientSpace A hA mu χ H hω hf hH)
  · intro hE
    apply Submodule.span_le.mpr
    rintro f ⟨ω, hω, hf, hH⟩
    exact hE ω hω f hf hH

/-- Equivalence with the exact finite-dimensional-container input of the VIII.5 reduction. -/
theorem finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_iff :
    FiniteDimensional ℂ (discreteSeriesCentralFixedCoefficientSpace.{uG, uV} A hA mu χ H) ↔
      ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧
        ∀ ω ∈ discreteSeriesCentralFixed.{uG, uV} A hA mu χ H,
          ∀ f ∈ coefficientFunctionSpace ω.val.out.obj, IsBiInvariant H f → f ∈ E := by
  constructor
  · intro h
    exact ⟨_, h, (discreteSeriesCentralFixedCoefficientSpace_le_iff A hA mu χ H _).mp le_rfl⟩
  · rintro ⟨E, hE, hmem⟩
    letI := hE
    exact Submodule.finiteDimensional_of_le
      ((discreteSeriesCentralFixedCoefficientSpace_le_iff A hA mu χ H E).mpr hmem)

end Coefficients

/-- The analytic fixed-coefficient finiteness obligation on actual rational points.
This is the consequence of VIII.4.1 and VIII.4.2 used in VIII.5, formulated without an
assumed finite-dimensional container, a cuspidal projection, or a spectral-finiteness premise. -/
def RationalFixedCoefficientFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s),
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      letI : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (H : OpenSubgroup (rationalPoints G)),
        IsCompact (H : Set (rationalPoints G)) →
        ∀ χ : (rationalPoints.map s).range →* ℂˣ, Continuous χ →
          (∀ a, ‖(χ a : ℂ)‖ = 1) →
          (∀ a : (rationalPoints.map s).range, (a : rationalPoints G) ∈ H → χ a = 1) →
          FiniteDimensional ℂ (discreteSeriesCentralFixedCoefficientSpace.{u, uV}
            (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
            mu χ H.toSubgroup)

/-- The fixed-coefficient target discharges precisely the remaining hypothesis of the
published rational-point reduction, giving Waldspurger's VIII.1.2 statement. -/
theorem RationalFixedCoefficientFinitenessStatement.orbitFiniteness
    (h : RationalFixedCoefficientFinitenessStatement.{u, uV}) :
    RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG T s hs
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
  letI := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ H hHo hHc
  exact finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional G s mu hG hs
    ⟨H, hHo⟩ hHc (fun χ hχ hu ht =>
      (finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_iff
        (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
        mu χ H).mp (h F G hG T s hs mu ⟨H, hHo⟩ hHc χ hχ hu ht))

end Langlands.HarishChandraSchwartz
