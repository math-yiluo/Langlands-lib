import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentDiagram
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation

/-! # The actual relative unit annulus and its canonical maps -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K)

/-- The single unit-annulus equation in relative two-variable unit-radius series. -/
def equations : Set (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :=
  {X (PositivePolyradius.unit (Fin 2)) A 0 *
    X (PositivePolyradius.unit (Fin 2)) A 1 - 1}

/-- The actual closed-equation quotient, retaining its inherited quotient norm. -/
abbrev Algebra :=
  RelativeRelations.QuotientAlgebra K A (PositivePolyradius.unit (Fin 2)) (equations K A)

/-- The contractive quotient projection. -/
def quotientMap :
    BoundedAlgHom K (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A)
      (Algebra K A) :=
  RelativeRelations.quotientMap K A _ (equations K A)

@[simp] theorem quotientMap_apply
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :
    quotientMap K A h = Ideal.Quotient.mk ((Ideal.span (equations K A)).closure) h := rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap K A) :=
  RelativeRelations.quotientMap_surjective K A _ (equations K A)

theorem quotientMap_eq_zero_iff
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :
    quotientMap K A h = 0 ↔ h ∈ (Ideal.span (equations K A)).closure :=
  RelativeRelations.quotientMap_eq_zero_iff K A _ (equations K A) h

theorem ker_quotientMap :
    RingHom.ker (quotientMap K A).toAlgHom = (Ideal.span (equations K A)).closure :=
  RelativeRelations.ker_quotientMap K A _ (equations K A)

theorem norm_quotientMap_le
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :
    ‖quotientMap K A h‖ ≤ ‖h‖ :=
  RelativeRelations.norm_quotientMap_le K A _ (equations K A) h

theorem exists_representative_norm_lt (a : Algebra K A) {ε : ℝ} (hε : 0 < ε) :
    ∃ h, quotientMap K A h = a ∧ ‖h‖ < ‖a‖ + ε :=
  RelativeRelations.exists_representative_norm_lt K A _ (equations K A) a hε

/-- The coefficient map, constant series followed by the quotient projection. -/
def baseMap : BoundedAlgHom K A (Algebra K A) :=
  RelativeRelations.baseMap K A _ (equations K A)

theorem baseMap_apply (a : A) :
    baseMap K A a = quotientMap K A
      (constantAlgHom (PositivePolyradius.unit (Fin 2)) K A a) := rfl

theorem baseMap_eq_algebraMap (a : A) :
    baseMap K A a = algebraMap A (Algebra K A) a := rfl

theorem norm_baseMap_le (a : A) : ‖baseMap K A a‖ ≤ ‖a‖ :=
  RelativeRelations.norm_baseMap_le K A _ (equations K A) a

/-- The two quotient coordinate images. -/
def coordinate (i : Fin 2) : Algebra K A :=
  RelativeRelations.newCoordinate K A _ (equations K A) i

theorem coordinate_def (i : Fin 2) :
    coordinate K A i = quotientMap K A (X (PositivePolyradius.unit (Fin 2)) A i) := rfl

theorem norm_coordinate_le (i : Fin 2) : ‖coordinate K A i‖ ≤ 1 :=
  RelativeRelations.norm_newCoordinate_le K A _ (equations K A) i

/-- The class of the first variable. -/
abbrev annulusX : Algebra K A := coordinate K A 0

/-- The class of the second variable, inverse to the first. -/
abbrev annulusY : Algebra K A := coordinate K A 1

theorem annulusX_def :
    annulusX K A = quotientMap K A (X (PositivePolyradius.unit (Fin 2)) A 0) := rfl

theorem annulusY_def :
    annulusY K A = quotientMap K A (X (PositivePolyradius.unit (Fin 2)) A 1) := rfl

theorem norm_annulusX_le : ‖annulusX K A‖ ≤ 1 := norm_coordinate_le K A 0

theorem norm_annulusY_le : ‖annulusY K A‖ ≤ 1 := norm_coordinate_le K A 1

/-- The empty-monomial bound also holds when the quotient is zero. -/
theorem norm_one_le : ‖(1 : Algebra K A)‖ ≤ 1 := by
  have h := norm_baseMap_le K A 1
  rw [show baseMap K A 1 = 1 from (baseMap K A).toAlgHom.map_one] at h
  exact h.trans (PresentedAffinoidAlgebra.norm_one_le K A)

/-- The defining unit relation in the actual quotient. -/
theorem annulusX_mul_annulusY : annulusX K A * annulusY K A = 1 := by
  have h := RelativeRelations.quotientMap_equation K A
    (PositivePolyradius.unit (Fin 2)) (equations K A)
    (Set.mem_singleton (X (PositivePolyradius.unit (Fin 2)) A 0 *
      X (PositivePolyradius.unit (Fin 2)) A 1 - 1))
  change (quotientMap K A).toAlgHom
    (X (PositivePolyradius.unit (Fin 2)) A 0 *
      X (PositivePolyradius.unit (Fin 2)) A 1 - 1) = 0 at h
  rw [map_sub, map_mul, map_one, sub_eq_zero] at h
  exact h

/-- Bounded maps out of the annulus are determined by coefficients and its two coordinates. -/
theorem hom_ext {B : Type v} [NormedCommRing B] [NormedAlgebra K B]
    (ψ χ : BoundedAlgHom K (Algebra K A) B)
    (hbase : ∀ a, ψ (baseMap K A a) = χ (baseMap K A a))
    (hX : ψ (annulusX K A) = χ (annulusX K A))
    (hY : ψ (annulusY K A) = χ (annulusY K A)) : ψ = χ := by
  have h := relative_hom_ext (PositivePolyradius.unit (Fin 2))
    (ψ.comp (quotientMap K A)) (χ.comp (quotientMap K A)) hbase
    (fun i => by
      fin_cases i
      · exact hX
      · exact hY)
  apply RelativeRelations.hom_ext K A _ (equations K A) B
  intro a
  exact congrArg (fun φ : BoundedAlgHom K _ B => φ a) h

/-- The two existing overlap coordinates, in their original order. -/
def overlapCoordinate (f : A) (i : Fin 2) : BinaryLaurent.Overlap K A f :=
  if i = 0 then BinaryLaurent.overlapX K A f else BinaryLaurent.overlapY K A f

@[simp] theorem overlapCoordinate_zero (f : A) :
    overlapCoordinate K A f 0 = BinaryLaurent.overlapX K A f := by
  simp [overlapCoordinate]

@[simp] theorem overlapCoordinate_one (f : A) :
    overlapCoordinate K A f 1 = BinaryLaurent.overlapY K A f := by
  simp [overlapCoordinate]

theorem norm_overlapCoordinate_le (f : A) (i : Fin 2) :
    ‖overlapCoordinate K A f i‖ ≤ 1 := by
  fin_cases i
  · simpa using BinaryLaurent.norm_overlapX_le K A f
  · simpa using BinaryLaurent.norm_overlapY_le K A f

section Maps

variable [CompleteSpace K]

/-- One-variable evaluation at either of the two annulus coordinates. -/
def oneVariable (i : Fin 2) :
    BoundedAlgHom K (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A)
      (Algebra K A) :=
  evaluateCoefficientsHom (PositivePolyradius.unit (Fin 1)) (baseMap K A)
    (fun _ => coordinate K A i) (norm_baseMap_le K A)
    (monomialValue_norm_le_weight (PositivePolyradius.unit (Fin 1)) (Algebra K A)
      (norm_one_le K A) (fun _ => coordinate K A i) (fun _ => norm_coordinate_le K A i))

theorem oneVariable_apply (i : Fin 2)
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    oneVariable K A i h =
      evaluateCoefficients (PositivePolyradius.unit (Fin 1)) (baseMap K A)
        (fun _ => coordinate K A i) h := rfl

@[simp] theorem oneVariable_constant (i : Fin 2) (a : A) :
    oneVariable K A i (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a) =
      baseMap K A a :=
  evaluateCoefficients_constant _ _ _ a

@[simp] theorem oneVariable_X (i : Fin 2) (j : Fin 1) :
    oneVariable K A i (X (PositivePolyradius.unit (Fin 1)) A j) = coordinate K A i :=
  evaluateCoefficients_X _ _ _ j

theorem norm_oneVariable_le (i : Fin 2)
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    ‖oneVariable K A i h‖ ≤ ‖h‖ :=
  norm_evaluateCoefficients_le _ _ _ (norm_baseMap_le K A)
    (monomialValue_norm_le_weight (PositivePolyradius.unit (Fin 1)) (Algebra K A)
      (norm_one_le K A) (fun _ => coordinate K A i) (fun _ => norm_coordinate_le K A i)) h

/-- The positive map evaluates the variable at the first coordinate. -/
abbrev positive := oneVariable K A 0

/-- The negative map evaluates the variable at the inverse coordinate. -/
abbrev negative := oneVariable K A 1

theorem positive_apply
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    positive K A h =
      evaluateCoefficients (PositivePolyradius.unit (Fin 1)) (baseMap K A)
        (fun _ => annulusX K A) h := rfl

theorem negative_apply
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    negative K A h =
      evaluateCoefficients (PositivePolyradius.unit (Fin 1)) (baseMap K A)
        (fun _ => annulusY K A) h := rfl

@[simp] theorem positive_constant (a : A) :
    positive K A (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a) =
      baseMap K A a := oneVariable_constant K A 0 a

@[simp] theorem negative_constant (a : A) :
    negative K A (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a) =
      baseMap K A a := oneVariable_constant K A 1 a

@[simp] theorem positive_X (j : Fin 1) :
    positive K A (X (PositivePolyradius.unit (Fin 1)) A j) = annulusX K A :=
  oneVariable_X K A 0 j

@[simp] theorem negative_X (j : Fin 1) :
    negative K A (X (PositivePolyradius.unit (Fin 1)) A j) = annulusY K A :=
  oneVariable_X K A 1 j

theorem norm_positive_le
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    ‖positive K A h‖ ≤ ‖h‖ := norm_oneVariable_le K A 0 h

theorem norm_negative_le
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    ‖negative K A h‖ ≤ ‖h‖ := norm_oneVariable_le K A 1 h

variable (f : A)

/-- Relative two-variable evaluation in the existing overlap quotient. -/
def toOverlapSeries :
    BoundedAlgHom K (GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A)
      (BinaryLaurent.Overlap K A f) :=
  evaluateCoefficientsHom (PositivePolyradius.unit (Fin 2))
    (BinaryLaurent.overlapBase K A f) (overlapCoordinate K A f)
    (BinaryLaurent.norm_overlapBase_le K A f)
    (monomialValue_norm_le_weight (PositivePolyradius.unit (Fin 2))
      (BinaryLaurent.Overlap K A f) (BinaryLaurent.norm_one_overlap_le K A f)
      (overlapCoordinate K A f) (norm_overlapCoordinate_le K A f))

@[simp] theorem toOverlapSeries_constant (a : A) :
    toOverlapSeries K A f (constantAlgHom (PositivePolyradius.unit (Fin 2)) K A a) =
      BinaryLaurent.overlapBase K A f a :=
  evaluateCoefficients_constant _ _ _ a

@[simp] theorem toOverlapSeries_X (i : Fin 2) :
    toOverlapSeries K A f (X (PositivePolyradius.unit (Fin 2)) A i) =
      overlapCoordinate K A f i :=
  evaluateCoefficients_X _ _ _ i

theorem norm_toOverlapSeries_le
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :
    ‖toOverlapSeries K A f h‖ ≤ ‖h‖ :=
  norm_evaluateCoefficients_le _ _ _ (BinaryLaurent.norm_overlapBase_le K A f)
    (monomialValue_norm_le_weight (PositivePolyradius.unit (Fin 2))
      (BinaryLaurent.Overlap K A f) (BinaryLaurent.norm_one_overlap_le K A f)
      (overlapCoordinate K A f) (norm_overlapCoordinate_le K A f)) h

/-- The existing overlap equations annihilate the unit-annulus equation. -/
theorem toOverlapSeries_equations :
    ∀ h ∈ equations K A, toOverlapSeries K A f h = 0 := by
  intro h hh
  rw [equations, Set.mem_singleton_iff] at hh
  subst h
  rw [map_sub, map_mul, map_one]
  change toOverlapSeries K A f (X (PositivePolyradius.unit (Fin 2)) A 0) *
    toOverlapSeries K A f (X (PositivePolyradius.unit (Fin 2)) A 1) - 1 = 0
  rw [toOverlapSeries_X, toOverlapSeries_X, overlapCoordinate_zero, overlapCoordinate_one,
    BinaryLaurent.overlapX_eq, BinaryLaurent.overlapBase_mul_overlapY, sub_self]

/-- The canonical contractive map from the annulus to the binary Laurent overlap. -/
def toOverlap : BoundedAlgHom K (Algebra K A) (BinaryLaurent.Overlap K A f) :=
  RelativeRelations.descend K A _ (equations K A) (BinaryLaurent.Overlap K A f)
    (toOverlapSeries K A f) (toOverlapSeries_equations K A f)

@[simp] theorem toOverlap_quotientMap
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :
    toOverlap K A f (quotientMap K A h) =
      evaluateCoefficients (PositivePolyradius.unit (Fin 2))
        (BinaryLaurent.overlapBase K A f) (overlapCoordinate K A f) h := rfl

@[simp] theorem toOverlap_baseMap (a : A) :
    toOverlap K A f (baseMap K A a) = BinaryLaurent.overlapBase K A f a := by
  rw [baseMap_apply, toOverlap_quotientMap, evaluateCoefficients_constant]

@[simp] theorem toOverlap_coordinate (i : Fin 2) :
    toOverlap K A f (coordinate K A i) = overlapCoordinate K A f i := by
  rw [coordinate_def, toOverlap_quotientMap, evaluateCoefficients_X]

@[simp] theorem toOverlap_annulusX :
    toOverlap K A f (annulusX K A) = BinaryLaurent.overlapX K A f :=
  (toOverlap_coordinate K A f 0).trans (overlapCoordinate_zero K A f)

@[simp] theorem toOverlap_annulusY :
    toOverlap K A f (annulusY K A) = BinaryLaurent.overlapY K A f :=
  (toOverlap_coordinate K A f 1).trans (overlapCoordinate_one K A f)

theorem norm_toOverlap_le (a : Algebra K A) : ‖toOverlap K A f a‖ ≤ ‖a‖ := by
  have h := RelativeRelations.norm_descend_le K A _ (equations K A)
    (BinaryLaurent.Overlap K A f) (toOverlapSeries K A f)
    (toOverlapSeries_equations K A f) 1 zero_lt_one
    (fun h => by simpa only [one_mul] using norm_toOverlapSeries_le K A f h) a
  simpa only [toOverlap, one_mul] using h

theorem toOverlap_comp_baseMap :
    (toOverlap K A f).comp (baseMap K A) = BinaryLaurent.overlapBase K A f :=
  BoundedAlgHom.ext (toOverlap_baseMap K A f)

/-- The positive composite agrees with the actual upper quotient followed by `left`. -/
theorem toOverlap_comp_positive :
    (toOverlap K A f).comp (positive K A) =
      (BinaryLaurent.left K A f).comp
        (RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1))
          1 (fun _ => f)) := by
  apply relative_hom_ext (PositivePolyradius.unit (Fin 1))
  · intro a
    change toOverlap K A f
      (positive K A (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a)) =
        BinaryLaurent.left K A f (BinaryLaurent.upperBase K A f a)
    rw [positive_constant, toOverlap_baseMap, BinaryLaurent.left_upperBase]
  · intro j
    rw [Subsingleton.elim j 0]
    change toOverlap K A f (positive K A (X (PositivePolyradius.unit (Fin 1)) A 0)) =
      BinaryLaurent.left K A f (BinaryLaurent.upperX K A f)
    rw [positive_X, toOverlap_annulusX, BinaryLaurent.left_upperX]

/-- The negative composite agrees with the actual lower quotient followed by `right`. -/
theorem toOverlap_comp_negative :
    (toOverlap K A f).comp (negative K A) =
      (BinaryLaurent.right K A f).comp
        (RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1))
          f (fun _ => 1)) := by
  apply relative_hom_ext (PositivePolyradius.unit (Fin 1))
  · intro a
    change toOverlap K A f
      (negative K A (constantAlgHom (PositivePolyradius.unit (Fin 1)) K A a)) =
        BinaryLaurent.right K A f (BinaryLaurent.lowerBase K A f a)
    rw [negative_constant, toOverlap_baseMap, BinaryLaurent.right_lowerBase]
  · intro j
    rw [Subsingleton.elim j 0]
    change toOverlap K A f (negative K A (X (PositivePolyradius.unit (Fin 1)) A 0)) =
      BinaryLaurent.right K A f (BinaryLaurent.lowerY K A f)
    rw [negative_X, toOverlap_annulusY, BinaryLaurent.right_lowerY]

theorem toOverlap_positive
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    toOverlap K A f (positive K A h) =
      BinaryLaurent.left K A f
        (RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1))
          1 (fun _ => f) h) :=
  congrArg (fun φ : BoundedAlgHom K _ (BinaryLaurent.Overlap K A f) => φ h)
    (toOverlap_comp_positive K A f)

theorem toOverlap_negative
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) :
    toOverlap K A f (negative K A h) =
      BinaryLaurent.right K A f
        (RelativeRationalPresentation.quotientMap K A (PositivePolyradius.unit (Fin 1))
          f (fun _ => 1) h) :=
  congrArg (fun φ : BoundedAlgHom K _ (BinaryLaurent.Overlap K A f) => φ h)
    (toOverlap_comp_negative K A f)

/-- The overlap map is determined among bounded maps by its displayed values. -/
theorem eq_toOverlap (ψ : BoundedAlgHom K (Algebra K A) (BinaryLaurent.Overlap K A f))
    (hbase : ∀ a, ψ (baseMap K A a) = BinaryLaurent.overlapBase K A f a)
    (hX : ψ (annulusX K A) = BinaryLaurent.overlapX K A f)
    (hY : ψ (annulusY K A) = BinaryLaurent.overlapY K A f) :
    ψ = toOverlap K A f :=
  hom_ext K A ψ (toOverlap K A f)
    (fun a => by rw [hbase, toOverlap_baseMap])
    (by rw [hX, toOverlap_annulusX])
    (by rw [hY, toOverlap_annulusY])

end Maps

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus
