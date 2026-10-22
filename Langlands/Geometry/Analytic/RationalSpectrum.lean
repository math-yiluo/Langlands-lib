import Langlands.Geometry.Analytic.RationalSpectrum.Statement
import Langlands.Geometry.Analytic.RationalPresentation
import Langlands.Geometry.Analytic.Spectrum.ResidueField
import Mathlib.Topology.Algebra.Algebra

/-! # Spectrum of the actual rational quotient -/

noncomputable section

universe u v w

namespace Langlands.Analytic



namespace RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra BanachSpectrum

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
  (g : StrictTateAlgebra (Fin n) K) (f : Fin m → StrictTateAlgebra (Fin n) K)

/-- Fractions in the actual completed residue field of a base point. -/
def residueFractions (x : BanachSpectrum (ofRelations K n S)) :
    Fin m → CompletedResidueField K x :=
  fun j => completedResidueMap K x (presentationMap K (ofRelations K n S) (f j)) /
    completedResidueMap K x (presentationMap K (ofRelations K n S) g)

omit [CompleteSpace K] in
theorem residueDenominator_ne_zero (hunit : GeneratesUnitIdeal K n m S g f)
    (x : BanachSpectrum (ofRelations K n S)) (hx : x ∈ locus K n m S g f) :
    completedResidueMap K x (presentationMap K (ofRelations K n S) g) ≠ 0 := by
  intro h
  apply denominator_ne_zero K n m S g f hunit x hx
  rw [← norm_completedResidueMap K x, h, norm_zero]

omit [CompleteSpace K] in
theorem residueFractions_bounded (hunit : GeneratesUnitIdeal K n m S g f)
    (x : BanachSpectrum (ofRelations K n S)) (hx : x ∈ locus K n m S g f) :
    HasBoundedMonomials (Fin m) (CompletedResidueField K x)
      (residueFractions K n m S g f x) := by
  apply hasBoundedMonomials_of_norm_le
  intro j
  change ‖completedResidueMap K x (presentationMap K (ofRelations K n S) (f j)) /
    completedResidueMap K x (presentationMap K (ofRelations K n S) g)‖ ≤ 1
  rw [norm_div, norm_completedResidueMap, norm_completedResidueMap]
  exact (div_le_one (lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _)
    (denominator_ne_zero K n m S g f hunit x hx).symm)).mpr (hx j)

omit [CompleteSpace K] in
theorem residueFractions_equations (hunit : GeneratesUnitIdeal K n m S g f)
    (x : BanachSpectrum (ofRelations K n S)) (hx : x ∈ locus K n m S g f) (j : Fin m) :
    completedResidueMap K x (presentationMap K (ofRelations K n S) g) *
      residueFractions K n m S g f x j =
        completedResidueMap K x (presentationMap K (ofRelations K n S) (f j)) := by
  exact mul_div_cancel₀ _ (residueDenominator_ne_zero K n m S g f hunit x hx)

/-- A point of the rational locus lifts by the actual fraction tuple in H(x). -/
def pointLift (hunit : GeneratesUnitIdeal K n m S g f)
    (x : BanachSpectrum (ofRelations K n S)) (hx : x ∈ locus K n m S g f) :
    BanachSpectrum (algebra K n m S g f) :=
  comap (liftFromBase K n m S g f (CompletedResidueField K x)
    (completedResidueMap K x) (residueFractions K n m S g f x)
    (residueFractions_bounded K n m S g f hunit x hx)
    (residueFractions_equations K n m S g f hunit x hx)).toBoundedRingHom
    (fieldPoint (CompletedResidueField K x))

theorem comap_pointLift (hunit : GeneratesUnitIdeal K n m S g f)
    (x : BanachSpectrum (ofRelations K n S)) (hx : x ∈ locus K n m S g f) :
    comap (baseMap K n m S g f).toBoundedRingHom
      (pointLift K n m S g f hunit x hx) = x := by
  apply BanachSpectrum.ext
  intro a
  have h := congrArg (fun φ => φ a)
    (liftFromBase_comp_baseMap K n m S g f (CompletedResidueField K x)
      (completedResidueMap K x) (residueFractions K n m S g f x)
      (residueFractions_bounded K n m S g f hunit x hx)
      (residueFractions_equations K n m S g f hunit x hx))
  change ‖liftFromBase K n m S g f (CompletedResidueField K x)
    (completedResidueMap K x) (residueFractions K n m S g f x)
    (residueFractions_bounded K n m S g f hunit x hx)
    (residueFractions_equations K n m S g f hunit x hx)
      (baseMap K n m S g f a)‖ = x a
  exact (congrArg norm h).trans (norm_completedResidueMap K x a)

theorem range_comap_baseMap (hunit : GeneratesUnitIdeal K n m S g f) :
    Set.range (comap (baseMap K n m S g f).toBoundedRingHom) = locus K n m S g f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact comap_mem_locus K n m S g f y
  · intro hx
    exact ⟨pointLift K n m S g f hunit x hx, comap_pointLift K n m S g f hunit x hx⟩

omit [CompleteSpace K] in
private theorem monomial_mem_of_coordinate_mem (T : PresentedStrictAffinoidAlgebra K)
    (C : Subalgebra K T) (hc : ∀ i, coordinate K T i ∈ C)
    (d : Fin T.arity →₀ ℕ) (c : K) :
    presentationMap K T (monomial (Fin T.arity) K d c) ∈ C := by
  rw [map_monomial]
  apply C.mul_mem (C.algebraMap_mem c)
  change (∏ i ∈ d.support, coordinate K T i ^ d i) ∈ C
  exact C.prod_mem fun i _ => C.pow_mem (hc i) _

/-- Algebraic fractions with powers of the denominator are dense in the
actual rational quotient. This follows from the coordinate equations
and convergent monomial expansions, without assuming domain representability. -/
theorem dense_fractionSubalgebra :
    Dense (fractionSubalgebra K (baseMap K n m S g f).toAlgHom
      (presentationMap K (ofRelations K n S) g) : Set (algebra K n m S g f)) := by
  let D := fractionSubalgebra K (baseMap K n m S g f).toAlgHom
    (presentationMap K (ofRelations K n S) g)
  let C := D.topologicalClosure
  have hcoord (i : Fin (n + m)) : coordinate K (algebra K n m S g f) i ∈ C := by
    apply Subalgebra.le_topologicalClosure
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact ⟨0, coordinate K (ofRelations K n S) i, by
        simpa only [pow_zero, one_mul] using (baseMap_coordinate K n m S g f i).symm⟩
    · exact ⟨1, presentationMap K (ofRelations K n S) (f j), by
        simpa only [pow_one] using coordinate_equation K n m S g f j⟩
  have hmon (d : Fin (n + m) →₀ ℕ) (c : K) :
      presentationMap K (algebra K n m S g f) (monomial (Fin (n + m)) K d c) ∈ C :=
    monomial_mem_of_coordinate_mem K (algebra K n m S g f) C hcoord d c
  intro a
  obtain ⟨h, rfl⟩ := presentationMap_surjective K (algebra K n m S g f) a
  change presentationMap K (algebra K n m S g f) h ∈ C
  apply (Subalgebra.isClosed_topologicalClosure _).mem_of_tendsto
    ((hasSum_monomials (Fin (n + m)) K h).mapL
      (presentationMap K (algebra K n m S g f)).toContinuousLinearMap)
  exact Filter.Eventually.of_forall fun s => C.sum_mem fun d _ => hmon d _

/-- Spectrum restriction is injective: on algebraic fractions its values
are forced, and those fractions are dense. -/
theorem comap_baseMap_injective (hunit : GeneratesUnitIdeal K n m S g f) :
    Function.Injective (comap (baseMap K n m S g f).toBoundedRingHom) := by
  intro x y h
  have hx : Continuous (fun a => x a) := by
    simpa only [norm_completedResidueMap] using (completedResidueMap K x).continuous.norm
  have hy : Continuous (fun a => y a) := by
    simpa only [norm_completedResidueMap] using (completedResidueMap K y).continuous.norm
  have hbase (a : ofRelations K n S) :
      x (baseMap K n m S g f a) = y (baseMap K n m S g f a) :=
    congrArg (fun z : BanachSpectrum (ofRelations K n S) => z a) h
  have hg : x (baseMap K n m S g f (presentationMap K (ofRelations K n S) g)) ≠ 0 :=
    denominator_ne_zero K n m S g f hunit
      (comap (baseMap K n m S g f).toBoundedRingHom x)
      (comap_mem_locus K n m S g f x)
  have heq : (fractionSubalgebra K (baseMap K n m S g f).toAlgHom
      (presentationMap K (ofRelations K n S) g) : Set (algebra K n m S g f)) ⊆
      {a | x a = y a} := by
    rintro a ⟨r, b, hb⟩
    have hxmul := congrArg x hb
    have hymul := congrArg y hb
    change x (_ ^ r * a) = x (baseMap K n m S g f b) at hxmul
    change y (_ ^ r * a) = y (baseMap K n m S g f b) at hymul
    rw [map_mul, map_pow] at hxmul hymul
    rw [← hbase] at hymul
    exact mul_left_cancel₀ (pow_ne_zero r hg)
      (hxmul.trans ((hbase b).trans hymul.symm))
  apply BanachSpectrum.ext
  intro a
  exact closure_minimal heq (isClosed_eq hx hy) (dense_fractionSubalgebra K n m S g f a)

/-- The rational quotient spectrum is a closed subspace, with the exact
norm-locus image given above. -/
theorem comap_baseMap_closedEmbedding (hunit : GeneratesUnitIdeal K n m S g f) :
    Topology.IsClosedEmbedding (comap (baseMap K n m S g f).toBoundedRingHom) :=
  (comapContinuous (baseMap K n m S g f).toBoundedRingHom).continuous.isClosedEmbedding
    (comap_baseMap_injective K n m S g f hunit)

/-- The constructed rational quotient has dense algebraic fractions and,
under the unit-ideal condition, exactly the prescribed closed spectrum locus. -/
theorem spectrumIdentification : SpectrumIdentificationStatement.{u} := by
  intro K _ _ _ n m S g f
  refine ⟨dense_fractionSubalgebra K n m S g f, fun hunit => ?_⟩
  exact ⟨range_comap_baseMap K n m S g f hunit,
    comap_baseMap_closedEmbedding K n m S g f hunit⟩

end RationalPresentation
end Langlands.Analytic
