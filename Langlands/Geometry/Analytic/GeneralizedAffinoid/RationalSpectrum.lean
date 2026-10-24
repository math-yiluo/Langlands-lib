import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectrumStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtension
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation
import Langlands.Geometry.Analytic.Spectrum.ResidueField
import Mathlib.Topology.Algebra.Algebra

/-! # Spectrum of the actual weighted rational quotient -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open GeneralizedTateAlgebra BanachSpectrum

/-- Entries bounded by the radii give the weighted monomial bound with
constant one, in any target whose unit has norm one. -/
theorem GeneralizedTateAlgebra.hasBoundedMonomials_of_norm_le {σ : Type u}
    (r : PositivePolyradius σ) (B : Type w) [NormedCommRing B] [NormOneClass B]
    (b : σ → B) (hb : ∀ i, ‖b i‖ ≤ r i) : HasBoundedMonomials r B b := by
  classical
  refine ⟨1, zero_lt_one, fun d => ?_⟩
  rw [one_mul]
  unfold StrictTateAlgebra.monomialValue PositivePolyradius.weight Finsupp.prod
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_prod₀
  · intro i _
    exact norm_nonneg _
  · intro i _
    exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hb i) _)

namespace PresentedAffinoidAlgebra.RationalPresentation

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- A subalgebra containing all quotient coordinates contains every
projected coefficient monomial. -/
theorem presentationMap_monomial_mem (T : PresentedAffinoidAlgebra K)
    (C : Subalgebra K T) (hc : ∀ i, coordinate K T i ∈ C)
    (d : Fin T.arity →₀ ℕ) (c : K) :
    presentationMap K T (monomial T.polyradius K d c) ∈ C := by
  rw [GeneralizedTateAlgebra.map_monomial T.polyradius K T (presentationMap K T) d c]
  apply C.mul_mem (C.algebraMap_mem c)
  unfold StrictTateAlgebra.monomialValue Finsupp.prod
  exact C.prod_mem fun i _ => C.pow_mem (hc i) _

/-- Algebraic fractions with powers of the denominator are dense in the
actual weighted rational quotient. No unit-ideal generation is used. -/
theorem dense_fractionSubalgebra :
    Dense (fractionSubalgebra K (baseMap K A s g f).toAlgHom
      (presentationMap K A g) : Set (algebra K A s g f)) := by
  let D := fractionSubalgebra K (baseMap K A s g f).toAlgHom (presentationMap K A g)
  let C := D.topologicalClosure
  have hcoord (i : Fin (A.arity + m)) : coordinate K (algebra K A s g f) i ∈ C := by
    apply Subalgebra.le_topologicalClosure
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact ⟨0, coordinate K A i, by
        simpa only [pow_zero, one_mul] using (baseMap_coordinate K A s g f i).symm⟩
    · refine ⟨1, presentationMap K A (f j), ?_⟩
      rw [pow_one]
      exact fraction_equation K A s g f j
  intro a
  obtain ⟨h, rfl⟩ := presentationMap_surjective K (algebra K A s g f) a
  change presentationMap K (algebra K A s g f) h ∈ C
  apply (Subalgebra.isClosed_topologicalClosure _).mem_of_tendsto
    ((hasSum_monomials _ K h).mapL
      (presentationMap K (algebra K A s g f)).toContinuousLinearMap)
  exact Filter.Eventually.of_forall fun t => C.sum_mem fun d _ =>
    presentationMap_monomial_mem K (algebra K A s g f) C hcoord d _

/-- Numerator-over-denominator fractions in the actual completed residue
field of a base point. -/
def residueFractions (x : BanachSpectrum A) : Fin m → CompletedResidueField K x :=
  fun j => completedResidueMap K x (presentationMap K A (f j)) /
    completedResidueMap K x (presentationMap K A g)

theorem residueDenominator_ne_zero (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum A) (hx : x ∈ locus K A s g f) :
    completedResidueMap K x (presentationMap K A g) ≠ 0 := by
  intro h
  apply denominator_ne_zero K A s g f hunit x hx
  rw [← norm_completedResidueMap K x, h, norm_zero]

theorem norm_residueFractions_le (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum A) (hx : x ∈ locus K A s g f) (j : Fin m) :
    ‖residueFractions K A g f x j‖ ≤ s j := by
  change ‖completedResidueMap K x (presentationMap K A (f j)) /
    completedResidueMap K x (presentationMap K A g)‖ ≤ s j
  rw [norm_div, norm_completedResidueMap, norm_completedResidueMap]
  exact (div_le_iff₀ (lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _)
    (denominator_ne_zero K A s g f hunit x hx).symm)).mpr (hx j)

theorem residueFractions_bounded (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum A) (hx : x ∈ locus K A s g f) :
    HasBoundedMonomials s (CompletedResidueField K x) (residueFractions K A g f x) :=
  hasBoundedMonomials_of_norm_le s _ _ (norm_residueFractions_le K A s g f hunit x hx)

theorem residueFractions_equations (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum A) (hx : x ∈ locus K A s g f) (j : Fin m) :
    completedResidueMap K x (presentationMap K A g) * residueFractions K A g f x j =
      completedResidueMap K x (presentationMap K A (f j)) :=
  mul_div_cancel₀ _ (residueDenominator_ne_zero K A s g f hunit x hx)

/-- A point of the weighted locus lifts through the bounded extension
determined by the actual fraction tuple in its completed residue field. -/
def pointLift (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum A) (hx : x ∈ locus K A s g f) :
    BanachSpectrum (algebra K A s g f) :=
  comap (liftFromBase K A s g f (CompletedResidueField K x)
    (completedResidueMap K x) (residueFractions K A g f x)
    (residueFractions_bounded K A s g f hunit x hx)
    (residueFractions_equations K A s g f hunit x hx)).toBoundedRingHom
    (fieldPoint (CompletedResidueField K x))

theorem spectrumMap_pointLift (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum A) (hx : x ∈ locus K A s g f) :
    spectrumMap K A s g f (pointLift K A s g f hunit x hx) = x := by
  apply BanachSpectrum.ext
  intro a
  have h := congrArg (fun φ => φ a)
    (liftFromBase_comp_baseMap K A s g f (CompletedResidueField K x)
      (completedResidueMap K x) (residueFractions K A g f x)
      (residueFractions_bounded K A s g f hunit x hx)
      (residueFractions_equations K A s g f hunit x hx))
  change ‖liftFromBase K A s g f (CompletedResidueField K x)
    (completedResidueMap K x) (residueFractions K A g f x)
    (residueFractions_bounded K A s g f hunit x hx)
    (residueFractions_equations K A s g f hunit x hx)
      (baseMap K A s g f a)‖ = x a
  exact (congrArg norm h).trans (norm_completedResidueMap K x a)

/-- Under generation, the spectrum map has exactly the weighted locus as range. -/
theorem range_spectrumMap (hunit : GeneratesUnitIdeal K A g f) :
    Set.range (spectrumMap K A s g f) = locus K A s g f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact spectrumMap_mem_locus K A s g f y
  · intro hx
    exact ⟨pointLift K A s g f hunit x hx, spectrumMap_pointLift K A s g f hunit x hx⟩

/-- Under generation, the spectrum map is injective: its values on algebraic
fractions are forced by cancelling a nonzero denominator power, and those
fractions are dense. -/
theorem spectrumMap_injective (hunit : GeneratesUnitIdeal K A g f) :
    Function.Injective (spectrumMap K A s g f) := by
  intro x y h
  have hx : Continuous (fun a => x a) := by
    simpa only [norm_completedResidueMap] using (completedResidueMap K x).continuous.norm
  have hy : Continuous (fun a => y a) := by
    simpa only [norm_completedResidueMap] using (completedResidueMap K y).continuous.norm
  have hbase (a : A) : x (baseMap K A s g f a) = y (baseMap K A s g f a) :=
    congrArg (fun z : BanachSpectrum A => z a) h
  have hg : x (baseMap K A s g f (presentationMap K A g)) ≠ 0 :=
    denominator_ne_zero K A s g f hunit (spectrumMap K A s g f x)
      (spectrumMap_mem_locus K A s g f x)
  have heq : (fractionSubalgebra K (baseMap K A s g f).toAlgHom
      (presentationMap K A g) : Set (algebra K A s g f)) ⊆ {a | x a = y a} := by
    rintro a ⟨r, b, hb⟩
    have hxmul := congrArg x hb
    have hymul := congrArg y hb
    change x (_ ^ r * a) = x (baseMap K A s g f b) at hxmul
    change y (_ ^ r * a) = y (baseMap K A s g f b) at hymul
    rw [map_mul, map_pow] at hxmul hymul
    rw [← hbase] at hymul
    exact mul_left_cancel₀ (pow_ne_zero r hg)
      (hxmul.trans ((hbase b).trans hymul.symm))
  apply BanachSpectrum.ext
  intro a
  exact closure_minimal heq (isClosed_eq hx hy) (dense_fractionSubalgebra K A s g f a)

/-- Under generation, the spectrum map is a closed embedding, since its
source is compact and its target Hausdorff. -/
theorem isClosedEmbedding_spectrumMap (hunit : GeneratesUnitIdeal K A g f) :
    Topology.IsClosedEmbedding (spectrumMap K A s g f) :=
  (spectrumMap K A s g f).continuous.isClosedEmbedding
    (spectrumMap_injective K A s g f hunit)

/-- All three clauses of the unchanged weighted spectrum identification target. -/
theorem spectrumIdentification : SpectrumIdentificationStatement.{u} := by
  intro K _ _ A m s g f
  exact ⟨dense_fractionSubalgebra K A s g f, fun hunit =>
    ⟨range_spectrumMap K A s g f hunit, isClosedEmbedding_spectrumMap K A s g f hunit⟩⟩

end PresentedAffinoidAlgebra.RationalPresentation
end Langlands.Analytic
