import Langlands.Global.CurvePlaceCompletedProduct
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.Adelic
import Mathlib.RingTheory.Valuation.IsTrivialOn

noncomputable section

universe u

open IsDedekindDomain
open scoped NumberField Classical

namespace Langlands.Global

section Curve

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L]

omit [Algebra k K] [IsScalarTower k K L] in
private theorem curvePlaceRestriction_nontrivial (q : AlgebraicCurve.Place k L) :
    (q.adicValuation.comap (algebraMap K L)).IsNontrivial := by
  by_contra hn
  let : q.adicValuation.IsTrivialOn K :=
    Valuation.IsTrivialOn.of_le_one _ fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · have h1 : q.adicValuation (algebraMap K L x) = 1 := by
          by_contra h1
          exact hn ⟨x, by simpa using hx, h1⟩
        exact h1.le
  obtain ⟨x, hx0, hx1⟩ :=
    Valuation.IsNontrivial.exists_val_nontrivial (v := q.adicValuation)
  exact (Valuation.transcendental_of_ne_one K x
    (fun hx => hx0 (hx ▸ map_zero _)) hx1)
      (Algebra.IsAlgebraic.isAlgebraic x)

/-- Restrict an actual upper curve place along the original finite field extension. -/
def curvePlaceRestriction (q : AlgebraicCurve.Place k L) : AlgebraicCurve.Place k K := by
  let v := q.adicValuation.comap (algebraMap K L)
  letI : v.IsNontrivial := curvePlaceRestriction_nontrivial q
  have he : v.valuationSubring = q.toValuationSubring.comap (algebraMap K L) := by
    ext x
    exact q.mem_iff_adicValuation_le_one.symm
  exact
    { toValuationSubring := q.toValuationSubring.comap (algebraMap K L)
      algebraMap_mem' := fun a => by
        change algebraMap K L (algebraMap k K a) ∈ q.toValuationSubring
        rw [← IsScalarTower.algebraMap_apply k K L]
        exact q.algebraMap_mem' a
      ne_top' := by
        rw [← he]
        intro h
        exact ((Valuation.valuationSubring_eq_top_iff v).mp h) inferInstance
      isPrincipalIdealRing' := by
        rw [← he]
        exact Valuation.valuationSubring_isPrincipalIdealRing v }

@[simp]
theorem curvePlaceRestriction_valuationSubring (q : AlgebraicCurve.Place k L) :
    (curvePlaceRestriction (K := K) q).toValuationSubring =
      q.toValuationSubring.comap (algebraMap K L) := rfl

@[simp]
theorem curvePlaceRestriction_mem_iff (q : AlgebraicCurve.Place k L) (x : K) :
    x ∈ (curvePlaceRestriction (K := K) q).toValuationSubring ↔
      algebraMap K L x ∈ q.toValuationSubring := Iff.rfl

/-- The full upper-place subtype is exactly the fiber of actual restriction. -/
theorem curvePlaceRestriction_eq_iff (q : AlgebraicCurve.Place k L)
    (p : AlgebraicCurve.Place k K) :
    curvePlaceRestriction q = p ↔
      q.toValuationSubring.comap (algebraMap K L) = p.toValuationSubring :=
  ⟨fun h => congrArg AlgebraicCurve.Place.toValuationSubring h,
    fun h => AlgebraicCurve.Place.ext h⟩

/-- Every lower place occurs as the restriction of an actual upper place. -/
theorem curvePlaceRestriction_surjective :
    Function.Surjective (curvePlaceRestriction (k := k) (K := K) (L := L)) := by
  intro p
  exact ⟨curvePlaceExtension p,
    (curvePlaceRestriction_eq_iff _ p).mpr (curvePlaceExtension_comap p)⟩

/-- The restriction map has finite fibers, including for inseparable extensions. -/
theorem curvePlaceRestriction_tendsto_cofinite :
    Filter.Tendsto (curvePlaceRestriction (k := k) (K := K) (L := L))
      Filter.cofinite Filter.cofinite := by
  apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
  intro p
  refine (Set.finite_range (fun q : CurvePlacesAbove k L p => q.1)).subset ?_
  intro q hq
  have h : curvePlaceRestriction q = p := hq
  exact ⟨⟨q, (curvePlaceRestriction_eq_iff q p).mp h⟩, rfl⟩

/-- All upper places above a finite lower exceptional set. -/
def curvePlaceExceptionalPreimage (S : Finset (AlgebraicCurve.Place k K)) :
    Finset (AlgebraicCurve.Place k L) := by
  have h : (curvePlaceRestriction (L := L) ⁻¹'
      (S : Set (AlgebraicCurve.Place k K))).Finite := by
    simpa using Filter.mem_cofinite.mp
      (curvePlaceRestriction_tendsto_cofinite (k := k) (K := K) (L := L)
        S.finite_toSet.compl_mem_cofinite)
  exact h.toFinset

@[simp]
theorem mem_curvePlaceExceptionalPreimage
    (S : Finset (AlgebraicCurve.Place k K)) (q : AlgebraicCurve.Place k L) :
    q ∈ curvePlaceExceptionalPreimage (L := L) S ↔ curvePlaceRestriction q ∈ S := by
  simp [curvePlaceExceptionalPreimage]

/-- Enlarge below to include a prescribed finite upper support in the full preimage. -/
theorem curvePlace_subset_exceptionalPreimage_union_image
    (S : Finset (AlgebraicCurve.Place k K)) (T : Finset (AlgebraicCurve.Place k L)) :
    T ⊆ curvePlaceExceptionalPreimage (L := L) (S ∪ T.image curvePlaceRestriction) := by
  classical
  intro q hq
  exact (mem_curvePlaceExceptionalPreimage _ q).mpr
    (Finset.mem_union_right S (Finset.mem_image_of_mem _ hq))

end Curve

section NumberField

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- All upper finite places above a finite lower exceptional set. -/
def numberFieldExceptionalPreimage (S : Finset (FinitePlace K)) :
    Finset (FinitePlace L) := by
  have h : (HeightOneSpectrum.under (𝓞 K) ⁻¹' (S : Set (FinitePlace K)) :
      Set (FinitePlace L)).Finite := by
    simpa using Filter.mem_cofinite.mp
      (AdelicFunctoriality.tendsto_under_cofinite (K := K) (L := L)
        S.finite_toSet.compl_mem_cofinite)
  exact h.toFinset

@[simp]
theorem mem_numberFieldExceptionalPreimage (S : Finset (FinitePlace K))
    (q : FinitePlace L) :
    q ∈ numberFieldExceptionalPreimage (L := L) S ↔ q.under (𝓞 K) ∈ S := by
  simp [numberFieldExceptionalPreimage]

/-- Enlarge below to include a prescribed finite upper support in the full preimage. -/
theorem numberField_subset_exceptionalPreimage_union_image
    (S : Finset (FinitePlace K)) (T : Finset (FinitePlace L)) :
    T ⊆ numberFieldExceptionalPreimage (L := L)
      (S ∪ T.image (HeightOneSpectrum.under (𝓞 K))) := by
  classical
  intro q hq
  exact (mem_numberFieldExceptionalPreimage _ q).mpr
    (Finset.mem_union_right S (Finset.mem_image_of_mem _ hq))

end NumberField

end Langlands.Global
