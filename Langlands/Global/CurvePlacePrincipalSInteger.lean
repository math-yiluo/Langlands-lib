import Langlands.Global.DedekindAwaySInteger
import Langlands.Global.FiniteConstantCurveChart
import Langlands.Global.CurvePlaceAdeleDiagonal

noncomputable section

universe u

open IsDedekindDomain IntermediateField AlgebraicCurve
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global.FiniteConstantCurveChart BigOperators

namespace Langlands.Global

variable (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The actual finite union of parameter poles and poles of an inverse denominator. -/
def curvePlacePrincipalExceptional (s t : K) : Finset (Place k K) := by
  classical
  exact (curvePlaceFinitePoles k K s).toFinset ∪ (curvePlaceFinitePoles k K t⁻¹).toFinset

@[simp]
theorem mem_curvePlacePrincipalExceptional (s t : K) (p : Place k K) :
    p ∈ curvePlacePrincipalExceptional k K s t ↔
      s ∉ p.toValuationSubring ∨ t⁻¹ ∉ p.toValuationSubring := by
  classical
  simp [curvePlacePrincipalExceptional]

variable (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) (ht : t ≠ 0)

/-- The actual outside-set ring is the actual principal localization of the normalized chart. -/
theorem curvePlacePrincipalSIntegers_eq :
    curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)) =
      (dedekindAwaySubalgebra (K := K) t ht).toSubring := by
  ext x
  constructor
  · intro hx
    apply (mem_dedekindAwaySubalgebra_iff t ht x).mpr
    intro P hP
    let p : Place k K := Place.ofHeightOneSpectrum (K := k) P
    have hs : s ∈ p.toValuationSubring :=
      (FiniteConstantCurveChart.primeEquivChartPlaces k K s P).property
    have hu : P.valuation K (t : K) = 1 := (P.valuation_eq_one_iff_notMem).mpr hP
    have hi : (t : K)⁻¹ ∈ p.toValuationSubring := by
      change (t : K)⁻¹ ∈ (Place.ofHeightOneSpectrum (K := k) P).toValuationSubring
      rw [Place.ofHeightOneSpectrum_toValuationSubring,
        Valuation.mem_valuationSubring_iff, map_inv₀, hu, inv_one]
    have hp : p ∉ curvePlacePrincipalExceptional k K s (t : K) := by
      simpa only [mem_curvePlacePrincipalExceptional, not_or, not_not] using And.intro hs hi
    have hx' := hx p hp
    simpa only [p, Place.ofHeightOneSpectrum_toValuationSubring,
      Valuation.mem_valuationSubring_iff] using hx'
  · rintro ⟨a, b, hb, rfl⟩ p hp
    have hreg : s ∈ p.toValuationSubring ∧ (t : K)⁻¹ ∈ p.toValuationSubring := by
      simpa only [mem_curvePlacePrincipalExceptional, not_or, not_not] using hp
    obtain ⟨n, rfl⟩ := hb
    change (a : K) * ((t : K) ^ n)⁻¹ ∈ p.toValuationSubring
    rw [← inv_pow]
    exact p.toValuationSubring.toSubring.mul_mem
      (CurveModel.chartRing_le_valuationSubring p.toValuationSubring
        p.algebraMap_mem' (Set.singleton_subset_iff.mpr hreg.1) a.property)
      (p.toValuationSubring.pow_mem hreg.2 n)

/-- The original chart localization and outside-set integers agree on every original field element. -/
def curvePlacePrincipalSIntegersEquiv :
    curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)) ≃+*
      dedekindAwaySubalgebra (K := K) t ht :=
  RingEquiv.subringCongr (curvePlacePrincipalSIntegers_eq k K s t ht)

@[simp]
theorem curvePlacePrincipalSIntegersEquiv_coe
    (x : curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) :
    (curvePlacePrincipalSIntegersEquiv k K s t ht x : K) = x := rfl

/-- These actual principal exceptional sets contain any prescribed finite set of original places. -/
theorem exists_curvePlacePrincipalExceptional_superset (S : Finset (Place k K)) :
    ∃ d : CurveModel.chartRing k ({s} : Set K), d ≠ 0 ∧
      S ⊆ curvePlacePrincipalExceptional k K s (d : K) := by
  classical
  let C := CurveModel.chartRing k ({s} : Set K)
  have H : ∀ p : S, ∃ a : C, a ≠ 0 ∧
      ∀ hs : s ∈ p.1.toValuationSubring,
        a ∈ CurveModel.centre k s p.1.toValuationSubring p.1.algebraMap_mem' hs := by
    intro p
    by_cases hs : s ∈ p.1.toValuationSubring
    · let P := CurveModel.primeOfValuationSubring k s p.1.toValuationSubring
        p.1.algebraMap_mem' hs p.1.ne_top'
      obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff P.asIdeal).mp P.ne_bot
      exact ⟨a, ha0, fun _ => ha⟩
    · exact ⟨1, one_ne_zero, fun h => False.elim (hs h)⟩
  choose a ha0 ha using H
  let d : C := ∏ p : S, a p
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => ha0 p
  refine ⟨d, hd, ?_⟩
  intro p hp
  apply (mem_curvePlacePrincipalExceptional k K s (d : K) p).mpr
  by_cases hs : s ∈ p.toValuationSubring
  · right
    have hval : p.toValuationSubring.valuation (d : K) < 1 := by
      change d ∈ CurveModel.centre k s p.toValuationSubring p.algebraMap_mem' hs
      exact Ideal.IsPrime.prod_mem_iff.mpr
        ⟨⟨p, hp⟩, Finset.mem_univ _, ha ⟨p, hp⟩ hs⟩
    have hd0 : (d : K) ≠ 0 := fun h => hd (Subtype.ext h)
    exact (p.toValuationSubring.mem_nonunits_iff_or.mp hval).resolve_left hd0
  · exact Or.inl hs

end Langlands.Global
