import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeEquationComparison
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Restriction along an affinoid coefficient-field presentation -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.ScalarRestriction

open GeneralizedTateAlgebra

variable (K L : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (S : PresentedAffinoidAlgebra K) (e : BoundedAlgEquiv K S L)
  (he : ∀ a, ‖e a‖ = ‖a‖) (R : PresentedAffinoidAlgebra L)
  [NormedAlgebra K R] [IsScalarTower K L R]

/-- The quotient presentation map with its original-field compatibility. -/
def quotientOverBase :
    BoundedAlgHom K (GeneralizedTateAlgebra R.polyradius L) R where
  toAlgHom := (presentationMap L R).toAlgHom.restrictScalars K
  bounded := (presentationMap L R).bounded

/-- Evaluate the coefficient presentation and retain the test coordinates. -/
def seriesMap :
    BoundedAlgHom K (GeneralizedTateAlgebra (S.polyradius.append R.polyradius) K)
      (GeneralizedTateAlgebra R.polyradius L) :=
  (mapCoefficientsAlgHom R.polyradius e.toBoundedAlgHom).comp
    (Adjoin.relativeSeriesEvaluation K S R.polyradius)

include he in
theorem norm_seriesMap_le
    (f : GeneralizedTateAlgebra (S.polyradius.append R.polyradius) K) :
    ‖seriesMap K L S e R f‖ ≤ ‖f‖ := by
  have h := norm_mapCoefficientsAlgHom_le R.polyradius e.toBoundedAlgHom zero_le_one
    (fun a => (he a).le.trans_eq (one_mul _).symm)
      (Adjoin.relativeSeriesEvaluation K S R.polyradius f)
  exact (h.trans_eq (one_mul _)).trans
    (Adjoin.norm_relativeSeriesEvaluation_le K S R.polyradius f)

@[simp] theorem seriesMap_appendLeft (f : GeneralizedTateAlgebra S.polyradius K) :
    seriesMap K L S e R (appendLeft S.polyradius R.polyradius K f) =
      constantAlgHom R.polyradius K L (e (presentationMap K S f)) := by
  change mapCoefficients R.polyradius e.toBoundedAlgHom.toBoundedRingHom
    (Adjoin.relativeSeriesEvaluation K S R.polyradius
      (appendLeft S.polyradius R.polyradius K f)) = _
  rw [Adjoin.relativeSeriesEvaluation_appendLeft]
  exact mapCoefficients_algebraMap R.polyradius e.toBoundedAlgHom.toBoundedRingHom _

@[simp] theorem seriesMap_newX (j : Fin R.arity) :
    seriesMap K L S e R
      (X (S.polyradius.append R.polyradius) K (Fin.natAdd S.arity j)) =
        X R.polyradius L j := by
  change mapCoefficients R.polyradius e.toBoundedAlgHom.toBoundedRingHom
    (Adjoin.relativeSeriesEvaluation K S R.polyradius _) = _
  rw [Adjoin.relativeSeriesEvaluation_X, Adjoin.relativeSeriesTuple_natAdd,
    mapCoefficients_X]

theorem seriesMap_surjective : Function.Surjective (seriesMap K L S e R) := by
  intro f
  let g := mapCoefficientsAlgHom R.polyradius e.symm.toBoundedAlgHom f
  obtain ⟨a, ha⟩ := Adjoin.relativeSeriesMap_surjective K S R.polyradius g
  obtain ⟨p, hp⟩ := presentationMap_surjective K (Adjoin.algebra K S R.polyradius ∅) a
  refine ⟨p, ?_⟩
  have hcoeff :
      (mapCoefficientsAlgHom R.polyradius e.toBoundedAlgHom).comp
        (mapCoefficientsAlgHom R.polyradius e.symm.toBoundedAlgHom) =
          BoundedAlgHom.id K (GeneralizedTateAlgebra R.polyradius L) := by
    rw [← mapCoefficientsAlgHom_comp]
    have h : e.toBoundedAlgHom.comp e.symm.toBoundedAlgHom = BoundedAlgHom.id K L :=
      BoundedAlgHom.ext (e.apply_symm_apply)
    rw [h, mapCoefficientsAlgHom_id]
  change mapCoefficientsAlgHom R.polyradius e.toBoundedAlgHom
    (Adjoin.relativeSeriesEvaluation K S R.polyradius p) = f
  have hp' : Adjoin.relativeSeriesEvaluation K S R.polyradius p = g := by
    exact (congrArg (Adjoin.relativeSeriesMap K S R.polyradius) hp).trans ha
  rw [hp']
  exact congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra R.polyradius L)
    (GeneralizedTateAlgebra R.polyradius L) => φ f) hcoeff

/-- An actual finite weighted `K` presentation of the test algebra. -/
def presentation : PresentedAffinoidAlgebra K where
  arity := S.arity + R.arity
  polyradius := S.polyradius.append R.polyradius
  ideal := R.ideal.comap (seriesMap K L S e R).toAlgHom.toRingHom
  ideal_closed := R.ideal_closed.preimage (seriesMap K L S e R).continuous

/-- The enlarged scalar presentation evaluated in the actual test quotient. -/
def evaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra (S.polyradius.append R.polyradius) K) R :=
  (quotientOverBase K L R).comp (seriesMap K L S e R)

/-- The forward map from the restricted presentation to the actual test. -/
def toTest : BoundedAlgHom K (presentation K L S e R) R := by
  letI := (presentation K L S e R).ideal_closed
  exact BoundedAlgHom.liftQuotient K (presentation K L S e R).ideal
    (evaluation K L S e R) (fun f hf => (presentationMap_eq_zero_iff L R _).mpr hf)

@[simp] theorem toTest_presentationMap
    (f : GeneralizedTateAlgebra (S.polyradius.append R.polyradius) K) :
    toTest K L S e R (presentationMap K (presentation K L S e R) f) =
      presentationMap L R (seriesMap K L S e R f) := rfl

/-- The coefficient presentation acts in the restricted presentation. -/
def coefficientBase : BoundedAlgHom K S (presentation K L S e R) := by
  letI := S.ideal_closed
  refine BoundedAlgHom.liftQuotient K S.ideal
    ((presentationMap K (presentation K L S e R)).comp
      (appendLeft S.polyradius R.polyradius K)) ?_
  intro f hf
  apply (presentationMap_eq_zero_iff K (presentation K L S e R) _).mpr
  change seriesMap K L S e R (appendLeft S.polyradius R.polyradius K f) ∈ R.ideal
  rw [seriesMap_appendLeft, (presentationMap_eq_zero_iff K S _).mpr hf]
  simpa only [map_zero] using R.ideal.zero_mem

@[simp] theorem coefficientBase_presentationMap (f : GeneralizedTateAlgebra S.polyradius K) :
    coefficientBase K L S e R (presentationMap K S f) =
      presentationMap K (presentation K L S e R)
        (appendLeft S.polyradius R.polyradius K f) := rfl

theorem norm_coefficientBase_le (a : S) :
    ‖coefficientBase K L S e R a‖ ≤ ‖a‖ := by
  letI := S.ideal_closed
  exact (BoundedAlgHom.quotient_norm_bound S.ideal
    (coefficientBase K L S e R).toAlgHom.toRingHom 1 zero_lt_one
    (fun f => by
      change ‖presentationMap K (presentation K L S e R)
        (appendLeft S.polyradius R.polyradius K f)‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact (norm_presentationMap_le K _ _).trans_eq
        (norm_appendLeft S.polyradius R.polyradius K f)) a).trans_eq (one_mul _)

/-- The actual extension-field scalar map into the restricted presentation. -/
def scalarMap : BoundedAlgHom K L (presentation K L S e R) :=
  (coefficientBase K L S e R).comp e.symm.toBoundedAlgHom

include he in
theorem norm_scalarMap_le (z : L) :
    ‖scalarMap K L S e R z‖ ≤ ‖z‖ := by
  exact (norm_coefficientBase_le K L S e R _).trans_eq
    ((he (e.symm z)).symm.trans (congrArg norm (e.apply_symm_apply z)))

/-- The test coordinates retain their specified positive radii. -/
def testTuple : Fin R.arity → presentation K L S e R :=
  fun j => coordinate K (presentation K L S e R) (Fin.natAdd S.arity j)

theorem testTuple_monomial_bound (d : Fin R.arity →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (presentation K L S e R)
      (testTuple K L S e R) d‖ ≤ R.polyradius.weight d := by
  apply monomialValue_norm_le_weight _ _ (norm_one_le K _) _
  intro j
  have h := norm_coordinate_le K (presentation K L S e R) (Fin.natAdd S.arity j)
  change ‖testTuple K L S e R j‖ ≤ (S.polyradius.append R.polyradius) (Fin.natAdd S.arity j) at h
  simpa only [PositivePolyradius.append_natAdd] using h

/-- Evaluate the test series through the actual scalar map. -/
def inverseEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra R.polyradius L) (presentation K L S e R) :=
  evaluateCoefficientsHom R.polyradius (scalarMap K L S e R)
    (testTuple K L S e R) (norm_scalarMap_le K L S e he R)
      (testTuple_monomial_bound K L S e R)

@[simp] theorem inverseEvaluation_constant (z : L) :
    inverseEvaluation K L S e he R (constantAlgHom R.polyradius K L z) =
      scalarMap K L S e R z :=
  evaluateCoefficients_constant _ _ _ z

@[simp] theorem inverseEvaluation_X (j : Fin R.arity) :
    inverseEvaluation K L S e he R (X R.polyradius L j) = testTuple K L S e R j :=
  evaluateCoefficients_X _ _ _ j

theorem inverseEvaluation_comp_seriesMap :
    (inverseEvaluation K L S e he R).comp (seriesMap K L S e R) =
      presentationMap K (presentation K L S e R) := by
  apply GeneralizedTateAlgebra.hom_ext
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    change inverseEvaluation K L S e he R
      (seriesMap K L S e R
        (X (S.polyradius.append R.polyradius) K (Fin.castAdd R.arity j))) = _
    rw [← appendLeft_X]
    rw [seriesMap_appendLeft, inverseEvaluation_constant]
    change coefficientBase K L S e R (e.symm (e (coordinate K S j))) = _
    rw [e.symm_apply_apply]
    exact coefficientBase_presentationMap K L S e R (X S.polyradius K j)
  · intro j
    change inverseEvaluation K L S e he R (seriesMap K L S e R _) = _
    rw [seriesMap_newX, inverseEvaluation_X]
    rfl

theorem inverseEvaluation_ideal (f : GeneralizedTateAlgebra R.polyradius L)
    (hf : f ∈ R.ideal) : inverseEvaluation K L S e he R f = 0 := by
  obtain ⟨p, rfl⟩ := seriesMap_surjective K L S e R f
  have h := congrArg (fun φ : BoundedAlgHom K
    (GeneralizedTateAlgebra (S.polyradius.append R.polyradius) K)
      (presentation K L S e R) => φ p) (inverseEvaluation_comp_seriesMap K L S e he R)
  exact h.trans ((presentationMap_eq_zero_iff K (presentation K L S e R) _).mpr hf)

/-- The bounded inverse descends through the entire test ideal. -/
def fromTest : BoundedAlgHom K R (presentation K L S e R) := by
  letI := R.ideal_closed
  let φ := BoundedAlgHom.liftQuotient K R.ideal (inverseEvaluation K L S e he R)
    (inverseEvaluation_ideal K L S e he R)
  refine ⟨{ toRingHom := φ.toAlgHom.toRingHom, commutes' := ?_ }, φ.bounded⟩
  intro c
  rw [IsScalarTower.algebraMap_apply K L R]
  change inverseEvaluation K L S e he R
    (constantAlgHom R.polyradius K L (algebraMap K L c)) = _
  rw [inverseEvaluation_constant]
  exact (scalarMap K L S e R).toAlgHom.commutes c

@[simp] theorem fromTest_presentationMap (f : GeneralizedTateAlgebra R.polyradius L) :
    fromTest K L S e he R (presentationMap L R f) = inverseEvaluation K L S e he R f := rfl

theorem fromTest_toTest (a : presentation K L S e R) :
    fromTest K L S e he R (toTest K L S e R a) = a := by
  obtain ⟨p, rfl⟩ := presentationMap_surjective K (presentation K L S e R) a
  change inverseEvaluation K L S e he R (seriesMap K L S e R p) = _
  exact congrArg (fun φ : BoundedAlgHom K
    (GeneralizedTateAlgebra (S.polyradius.append R.polyradius) K)
      (presentation K L S e R) => φ p) (inverseEvaluation_comp_seriesMap K L S e he R)

theorem toTest_fromTest (a : R) :
    toTest K L S e R (fromTest K L S e he R a) = a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective L R a
  obtain ⟨p, rfl⟩ := seriesMap_surjective K L S e R f
  have h := fromTest_toTest K L S e he R
    (presentationMap K (presentation K L S e R) p)
  rw [toTest_presentationMap] at h
  exact (congrArg (toTest K L S e R) h).trans (toTest_presentationMap K L S e R p)

/-- Actual bounded restriction of an affinoid test along an affinoid field presentation. -/
def boundedEquiv : BoundedAlgEquiv K (presentation K L S e R) R :=
  BoundedAlgEquiv.ofHomInv (toTest K L S e R) (fromTest K L S e he R)
    (fromTest_toTest K L S e he R) (toTest_fromTest K L S e he R)

end Langlands.Analytic.PresentedAffinoidAlgebra.ScalarRestriction
