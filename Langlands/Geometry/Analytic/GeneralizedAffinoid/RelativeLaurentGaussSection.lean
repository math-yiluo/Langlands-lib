import Langlands.Geometry.Analytic.GeneralizedAffinoid.LaurentGaussPresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.LaurentGaussNorm
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Definitions

/-! # Gauss points on an actual relative Laurent annulus -/

noncomputable section

universe u

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (t : ℝ) [Fact (0 < t)]

/-- The new-variable inverse equation in the actual enlarged scalar series ring. -/
def relation : GeneralizedTateAlgebra (A.polyradius.append (LaurentAnnulus.radii t)) K :=
  X (A.polyradius.append (LaurentAnnulus.radii t)) K (Fin.natAdd A.arity (0 : Fin 2)) *
    X (A.polyradius.append (LaurentAnnulus.radii t)) K (Fin.natAdd A.arity (1 : Fin 2)) - 1

/-- Adjoin a variable and its inverse with reciprocal prescribed radii. -/
abbrev algebra : PresentedAffinoidAlgebra K :=
  Adjoin.algebra K A (LaurentAnnulus.radii t) {relation K A t}

/-- The actual structural map of the relative annulus. -/
def baseMap : BoundedAlgHom K A (algebra K A t) :=
  Adjoin.baseMap K A (LaurentAnnulus.radii t) {relation K A t}

/-- The residue-field Laurent completion, viewed as a normed algebra over `K`. -/
def Fiber (x : BanachSpectrum A) : Type u :=
  CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t

instance (x : BanachSpectrum A) : NormedCommRing (Fiber K A t x) :=
  inferInstanceAs
    (NormedCommRing (CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t))

instance (x : BanachSpectrum A) : NormedAlgebra K (Fiber K A t x) where
  __ := ((CompletedGaussLaurent.ι (t := t)).comp
    (algebraMap K (BanachSpectrum.CompletedResidueField K x))).toAlgebra
  norm_smul_le c b := by
    have h := norm_mul_le
      (CompletedGaussLaurent.ι (t := t)
        (algebraMap K (BanachSpectrum.CompletedResidueField K x) c))
      (show CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t from b)
    rw [CompletedGaussLaurent.norm_ι, norm_algebraMap'] at h
    exact h

instance (x : BanachSpectrum A) : IsUltrametricDist (Fiber K A t x) :=
  inferInstanceAs
    (IsUltrametricDist (CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t))

instance (x : BanachSpectrum A) : CompleteSpace (Fiber K A t x) :=
  inferInstanceAs
    (CompleteSpace (CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t))

/-- Evaluate coefficients in the completed residue field, then include them as constants. -/
def coefficientMap (x : BanachSpectrum A) : BoundedAlgHom K A (Fiber K A t x) where
  toRingHom := (CompletedGaussLaurent.ι (t := t)).comp
    (BanachSpectrum.completedResidueMap K x).toAlgHom.toRingHom
  commutes' _ := rfl
  bounded := ⟨1, zero_lt_one, fun a => by
    change ‖(CompletedGaussLaurent.ι (t := t)
      (BanachSpectrum.completedResidueMap K x a) :
        CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t)‖ ≤ 1 * ‖a‖
    rw [CompletedGaussLaurent.norm_ι, one_mul]
    change ‖(BanachSpectrum.residueFieldMap K x a :
      BanachSpectrum.CompletedResidueField K x)‖ ≤ ‖a‖
    rw [UniformSpace.Completion.norm_coe, BanachSpectrum.norm_residueFieldMap]
    exact x.le_norm a⟩

theorem norm_coefficientMap (x : BanachSpectrum A) (a : A) :
    ‖coefficientMap K A t x a‖ = x a := by
  change ‖(CompletedGaussLaurent.ι (t := t)
    (BanachSpectrum.completedResidueMap K x a) :
      CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t)‖ = x a
  rw [CompletedGaussLaurent.norm_ι]
  change ‖(BanachSpectrum.residueFieldMap K x a :
    BanachSpectrum.CompletedResidueField K x)‖ = x a
  rw [UniformSpace.Completion.norm_coe, BanachSpectrum.norm_residueFieldMap]

theorem norm_coefficientMap_le (x : BanachSpectrum A) (a : A) :
    ‖coefficientMap K A t x a‖ ≤ ‖a‖ :=
  (norm_coefficientMap K A t x a).le.trans (x.le_norm a)

/-- The Laurent variable and inverse in the fiber with its restricted scalars. -/
def fiberTuple (x : BanachSpectrum A) : Fin 2 → Fiber K A t x :=
  LaurentAnnulus.completionTuple (BanachSpectrum.CompletedResidueField K x) t

theorem fiberTuple_monomial_bound (x : BanachSpectrum A) (d : Fin 2 →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (Fiber K A t x) (fiberTuple K A t x) d‖ ≤
      (LaurentAnnulus.radii t).weight d :=
  LaurentAnnulus.completionTuple_monomial_bound (BanachSpectrum.CompletedResidueField K x) t d

/-- Contractive evaluation of relative series in the residue-field Laurent completion. -/
def coefficientEvaluation (x : BanachSpectrum A) :
    BoundedAlgHom K (GeneralizedTateAlgebra (LaurentAnnulus.radii t) A) (Fiber K A t x) :=
  evaluateCoefficientsHom (K := K) (A := A) (B := Fiber K A t x)
    (LaurentAnnulus.radii t) (coefficientMap K A t x) (fiberTuple K A t x)
    (norm_coefficientMap_le K A t x)
    (fiberTuple_monomial_bound K A t x)

@[simp] theorem coefficientEvaluation_constant (x : BanachSpectrum A) (a : A) :
    coefficientEvaluation K A t x (constantAlgHom (LaurentAnnulus.radii t) K A a) =
      coefficientMap K A t x a :=
  evaluateCoefficients_constant (LaurentAnnulus.radii t) (coefficientMap K A t x)
    (fiberTuple K A t x) a

@[simp] theorem coefficientEvaluation_X (x : BanachSpectrum A) (i : Fin 2) :
    coefficientEvaluation K A t x (X (LaurentAnnulus.radii t) A i) =
      LaurentAnnulus.completionTuple (BanachSpectrum.CompletedResidueField K x) t i :=
  evaluateCoefficients_X (LaurentAnnulus.radii t) (coefficientMap K A t x)
    (fiberTuple K A t x) i

theorem norm_coefficientEvaluation_le (x : BanachSpectrum A)
    (f : GeneralizedTateAlgebra (LaurentAnnulus.radii t) A) :
    ‖coefficientEvaluation K A t x f‖ ≤ ‖f‖ :=
  norm_evaluateCoefficients_le (LaurentAnnulus.radii t) (coefficientMap K A t x)
    (fiberTuple K A t x) (norm_coefficientMap_le K A t x)
    (fiberTuple_monomial_bound K A t x) f

variable [CompleteSpace K]

/-- First pass from the enlarged scalar series to relative series, then evaluate. -/
def seriesEvaluation (x : BanachSpectrum A) :
    BoundedAlgHom K (GeneralizedTateAlgebra (A.polyradius.append (LaurentAnnulus.radii t)) K)
      (Fiber K A t x) :=
  (coefficientEvaluation K A t x).comp
    (Adjoin.relativeSeriesEvaluation K A (LaurentAnnulus.radii t))

@[simp] theorem seriesEvaluation_appendLeft (x : BanachSpectrum A)
    (f : GeneralizedTateAlgebra A.polyradius K) :
    seriesEvaluation K A t x (appendLeft A.polyradius (LaurentAnnulus.radii t) K f) =
      coefficientMap K A t x (presentationMap K A f) := by
  change coefficientEvaluation K A t x
    (Adjoin.relativeSeriesEvaluation K A (LaurentAnnulus.radii t) _) = _
  rw [Adjoin.relativeSeriesEvaluation_appendLeft, coefficientEvaluation_constant]

@[simp] theorem seriesEvaluation_newX (x : BanachSpectrum A) (i : Fin 2) :
    seriesEvaluation K A t x
      (X (A.polyradius.append (LaurentAnnulus.radii t)) K (Fin.natAdd A.arity i)) =
      LaurentAnnulus.completionTuple (BanachSpectrum.CompletedResidueField K x) t i := by
  change coefficientEvaluation K A t x
    (Adjoin.relativeSeriesEvaluation K A (LaurentAnnulus.radii t) _) = _
  rw [Adjoin.relativeSeriesEvaluation_X, Adjoin.relativeSeriesTuple_natAdd,
    coefficientEvaluation_X]

theorem seriesEvaluation_relation (x : BanachSpectrum A) :
    seriesEvaluation K A t x (relation K A t) = 0 := by
  change (seriesEvaluation K A t x).toAlgHom (_ * _ - 1) = 0
  rw [map_sub, map_mul, map_one, seriesEvaluation_newX, seriesEvaluation_newX]
  change (CompletedGaussLaurent.X *
    (↑(CompletedGaussLaurent.variableUnit⁻¹ :
      (CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t)ˣ) :
      CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t) - 1 :
      CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t) = 0
  exact sub_eq_zero.mpr
    (CompletedGaussLaurent.variableUnit :
      (CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t)ˣ).mul_inv

theorem seriesEvaluation_relations (x : BanachSpectrum A)
    (f : GeneralizedTateAlgebra (A.polyradius.append (LaurentAnnulus.radii t)) K)
    (hf : f ∈ Adjoin.relations K A (LaurentAnnulus.radii t) {relation K A t}) :
    seriesEvaluation K A t x f = 0 := by
  rcases hf with ⟨g, hg, rfl⟩ | hf
  · rw [seriesEvaluation_appendLeft, (presentationMap_eq_zero_iff K A g).mpr hg, map_zero]
  · rcases Set.mem_singleton_iff.mp hf with rfl
    exact seriesEvaluation_relation K A t x

theorem norm_seriesEvaluation_le (x : BanachSpectrum A)
    (f : GeneralizedTateAlgebra (A.polyradius.append (LaurentAnnulus.radii t)) K) :
    ‖seriesEvaluation K A t x f‖ ≤ ‖f‖ :=
  (norm_coefficientEvaluation_le K A t x _).trans
    (Adjoin.norm_relativeSeriesEvaluation_le K A (LaurentAnnulus.radii t) f)

/-- Evaluate the actual closed quotient, including both old and new relations. -/
def evaluation (x : BanachSpectrum A) : BoundedAlgHom K (algebra K A t) (Fiber K A t x) :=
  descendRelations K (A.arity + 2) (A.polyradius.append (LaurentAnnulus.radii t))
    (Adjoin.relations K A (LaurentAnnulus.radii t) {relation K A t}) (Fiber K A t x)
    (seriesEvaluation K A t x) (seriesEvaluation_relations K A t x)

@[simp] theorem evaluation_presentationMap (x : BanachSpectrum A)
    (f : GeneralizedTateAlgebra (A.polyradius.append (LaurentAnnulus.radii t)) K) :
    evaluation K A t x (presentationMap K (algebra K A t) f) =
      seriesEvaluation K A t x f := rfl

@[simp] theorem evaluation_baseMap (x : BanachSpectrum A) (a : A) :
    evaluation K A t x (baseMap K A t a) = coefficientMap K A t x a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  change evaluation K A t x (Adjoin.baseMap K A _ _ (presentationMap K A f)) = _
  rw [Adjoin.baseMap_presentationMap, evaluation_presentationMap, seriesEvaluation_appendLeft]

theorem norm_evaluation_le (x : BanachSpectrum A) (b : algebra K A t) :
    ‖evaluation K A t x b‖ ≤ ‖b‖ := by
  have h := norm_descendRelations_le K (A.arity + 2)
    (A.polyradius.append (LaurentAnnulus.radii t))
    (Adjoin.relations K A (LaurentAnnulus.radii t) {relation K A t}) (Fiber K A t x)
    (seriesEvaluation K A t x) (seriesEvaluation_relations K A t x) 1 zero_lt_one
    (fun f => by simpa only [one_mul] using norm_seriesEvaluation_le K A t x f) b
  change ‖evaluation K A t x b‖ ≤ 1 * ‖b‖ at h
  exact h.trans_eq (one_mul _)

/-- The norm-valued Gauss point in each completed-residue-field Laurent algebra. -/
def fiberPoint (x : BanachSpectrum A) : BanachSpectrum (Fiber K A t x) :=
  CompletedGaussLaurent.gaussPoint

/-- The canonical Gauss point above a given point of the original spectrum. -/
def sectionPoint (x : BanachSpectrum A) : BanachSpectrum (algebra K A t) :=
  BanachSpectrum.comap (evaluation K A t x).toBoundedRingHom (fiberPoint K A t x)

@[simp] theorem sectionPoint_apply (x : BanachSpectrum A) (b : algebra K A t) :
    sectionPoint K A t x b = ‖evaluation K A t x b‖ := rfl

@[simp] theorem sectionPoint_baseMap (x : BanachSpectrum A) (a : A) :
    sectionPoint K A t x (baseMap K A t a) = x a := by
  rw [sectionPoint_apply, evaluation_baseMap, norm_coefficientMap]

/-- Restriction from the actual annulus spectrum back to its base. -/
def restriction : C(BanachSpectrum (algebra K A t), BanachSpectrum A) :=
  BanachSpectrum.comapContinuous (baseMap K A t).toBoundedRingHom

@[simp] theorem restriction_sectionPoint (x : BanachSpectrum A) :
    restriction K A t (sectionPoint K A t x) = x := by
  apply BanachSpectrum.ext
  intro a
  exact sectionPoint_baseMap K A t x a

theorem restriction_surjective : Function.Surjective (restriction K A t) :=
  fun x => ⟨sectionPoint K A t x, restriction_sectionPoint K A t x⟩

end Langlands.Analytic.RelativeLaurentAnnulus
