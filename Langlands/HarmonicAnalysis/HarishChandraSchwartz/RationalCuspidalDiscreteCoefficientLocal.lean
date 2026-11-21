import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalRankZero

/-! # The local step for Waldspurger VIII.4.2

For one rational group and one Schwartz realization, the proper-radical convergence
input and the compact basis and Cartan data suffice for the lower inclusion. Local
finite dimensionality of the central level spans supplies the other inclusion,
without an all-groups VIII.4.1 hypothesis.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- The proper standard radical integrals converge absolutely for every element of
this Schwartz realization and all two-sided translates, for every radical Haar measure. -/
def RationalSchwartzProperRadicalConvergence : Prop :=
  ∀ (I : Finset (SimpleRoot i ν)), rootSet i ν I ≠ simpleRelativeRoots i ν →
    ∀ (muU : Measure (standardUnipotentPoints i ν (rootSet i ν I))) [muU.IsHaarMeasure]
      (φ : RationalSchwartzSpace hKc hPK ρ) (x y : rationalPoints G),
      Integrable (fun v : standardUnipotentPoints i ν (rootSet i ν I) =>
        (φ : rationalPoints G → ℂ) (x * v * y)) muU

/-- The closed convergence statement supplies the local input at any chosen realization. -/
theorem RationalSchwartzConstantTermConvergenceStatement.properRadicalConvergence
    (h : RationalSchwartzConstantTermConvergenceStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (hρ : IsClosedSubgroup ρ) :
    RationalSchwartzProperRadicalConvergence hKc hPK ρ :=
  fun I hI muU _ φ x y => h F G hG S i hi ν hν K hKc hPK N ρ hρ φ I hI muU x y

/-- The local lower inclusion of VIII.4.2 at independent carrier universe `uV`.
The actual compact subgroup with simultaneous standard basis and a finite Cartan
covering supplies the decay inputs to the direct cusp lift. Proper-radical
convergence for the fixed realization is the only convergence premise. -/
theorem rationalCuspidalCentralImage_superset_of_specialCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (hρ : IsClosedSubgroup ρ)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    (hconv : RationalSchwartzProperRadicalConvergence hKc hPK ρ)
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure] :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
      (discreteSeriesCentralCoefficientSpace.{u, uV}
        (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
        mu χ : Set (rationalPoints G → ℂ)) ⊆ rationalCuspidalCentralImage hKc hPK ρ muA χ := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu
  have hc : CentralIntegralConvergesOn (rationalCuspidalSubmodule hKc hPK ρ) muA χ :=
    fun φ _ g => rationalSchwartzCentralConvergence F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs
      muA χ hχ hu φ Submodule.mem_top g
  have hspan := coe_schwartzCentralIntegralSpan_eq_image _ _ _ hc
  have hle : discreteSeriesCentralCoefficientSpace.{u, uV} (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center mu χ ≤
        schwartzCentralIntegralSpan (rationalCuspidalSubmodule hKc hPK ρ) muA χ := by
    refine (discreteSeriesCentralCoefficientSpace_le_iff _ _ _ _ _).mpr ?_
    intro ω hω f hf
    have hsq := ω.property
    rw [← Quotient.out_eq ω.val] at hsq
    rw [← Quotient.out_eq ω.val] at hω
    obtain ⟨φ, hφ, hφf, -⟩ := DiscreteCoefficientCuspLift.exists_cuspidal_lift
      hG hi hν hK0c hbasis hcover hKc hPK ρ hs muA mu χ ω.val.out.obj hsq hω hconv f hf
    exact Submodule.subset_span ⟨φ, hφ, hφf⟩
  intro f hf
  exact (Set.ext_iff.mp hspan f).mp (hle hf)

/-- **VIII.4.2 for one group and one central character.** Give a compact open
`K0` with simultaneous standard basis and a finite Cartan covering, convergence
for the proper radicals of this Schwartz realization, and finite dimensionality
of its `χ`-level span at each compact open subgroup. Then the raw cuspidal
central image equals the canonical coefficient sum at carrier universe `max u uV`. -/
theorem rationalCuspidalCentralImage_eq_of_specialCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) (hρ : IsClosedSubgroup ρ)
    {K0 : Subgroup (rationalPoints G)} (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0) (hcover : FiniteCartanCovering F i ν K0)
    (hconv : RationalSchwartzProperRadicalConvergence hKc hPK ρ)
    (hs : IsSplitComponent s) (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure] :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (χ : (rationalPoints.map s).range →* ℂˣ), Continuous χ → IsUnitaryCharacter χ →
      (∀ J : OpenSubgroup (rationalPoints G), IsCompact (J : Set (rationalPoints G)) →
        FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ J.toSubgroup)) →
      rationalCuspidalCentralImage hKc hPK ρ muA χ =
        (discreteSeriesCentralCoefficientSpace.{u, max u uV}
          (rationalPoints.map s).range hs.isCentralSplitTorus.isCentral.range_le_center
          mu χ : Set (rationalPoints G → ℂ)) := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ χ hχ hu hfinite
  exact Set.Subset.antisymm
    (rationalCuspidalCentralImage_subset_of_specialCompact.{u, uV}
      hG hi hν hK0o hK0c hbasis hcover hKc hPK ρ hρ hs muA mu χ hχ hu hfinite)
    (rationalCuspidalCentralImage_superset_of_specialCompact.{u, max u uV}
      hKc hPK ρ hG hi hν hρ hK0c hbasis hcover hconv hs muA mu χ hχ hu)

end Langlands.HarishChandraSchwartz
