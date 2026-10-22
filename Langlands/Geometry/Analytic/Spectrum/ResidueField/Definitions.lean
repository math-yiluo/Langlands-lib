import Langlands.Geometry.Analytic.Spectrum.Properties
import Langlands.Geometry.Analytic.Spectrum.Nonarchimedean
import Mathlib.RingTheory.Valuation.Quotient
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Langlands.Geometry.Analytic.Affinoid

/-! # Valuations and residue fields of actual spectrum points -/

noncomputable section

universe u v

namespace Langlands.Analytic

open scoped NNReal

namespace BanachSpectrum

variable {A : Type u} [NormedCommRing A]
  {K : Type v} [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]

variable (K)

/-- The nonnegative-real valuation associated to the actual spectrum seminorm. -/
def toValuation (x : BanachSpectrum A) : Valuation A ℝ≥0 where
  toFun a := ⟨x a, apply_nonneg x.toMulRingSeminorm a⟩
  map_zero' := Subtype.ext (map_zero x.toMulRingSeminorm)
  map_one' := Subtype.ext (map_one x.toMulRingSeminorm)
  map_mul' a b := Subtype.ext (map_mul x.toMulRingSeminorm a b)
  map_add_le_max' a b := x.isNonarchimedean (K := K) a b

/-- The actual integral domain obtained by quotienting by the point's kernel. -/
def ResidueDomain (x : BanachSpectrum A) := A ⧸ x.kernel

instance (x : BanachSpectrum A) : CommRing (ResidueDomain x) :=
  inferInstanceAs (CommRing (A ⧸ x.kernel))

instance (x : BanachSpectrum A) : IsDomain (ResidueDomain x) := by
  let := kernel_isPrime x
  exact inferInstanceAs (IsDomain (A ⧸ x.kernel))

/-- The quotient map to the domain cut out by the actual seminorm kernel. -/
def residueQuotient (x : BanachSpectrum A) : A →+* ResidueDomain x :=
  Ideal.Quotient.mk x.kernel

/-- The valuation descends through its kernel; no norm on the quotient is assumed. -/
def residueValuation (x : BanachSpectrum A) : Valuation (ResidueDomain x) ℝ≥0 :=
  (toValuation K x).onQuot (J := x.kernel) (fun _ ha => Subtype.ext ha)

@[simp]
theorem residueValuation_quotient (x : BanachSpectrum A) (a : A) :
    (residueValuation K x (residueQuotient x a) : ℝ) = x a := rfl

theorem residueValuation_eq_zero (x : BanachSpectrum A) (a : ResidueDomain x) :
    residueValuation K x a = 0 ↔ a = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := x.kernel) a
  change (⟨x a, apply_nonneg x.toMulRingSeminorm a⟩ : ℝ≥0) = 0 ↔
    (Ideal.Quotient.mk x.kernel a : A ⧸ x.kernel) = 0
  exact NNReal.coe_eq_zero.symm.trans
    (Ideal.Quotient.eq_zero_iff_mem (I := x.kernel) (a := a)).symm

/-- The algebraic residue field is the genuine fraction field of the kernel quotient. -/
abbrev ResidueFraction (x : BanachSpectrum A) := FractionRing (ResidueDomain x)

theorem residueDenominators (x : BanachSpectrum A) :
    nonZeroDivisors (ResidueDomain x) ≤ (residueValuation K x).supp.primeCompl :=
  fun a ha hz => (nonZeroDivisors.ne_zero ha) ((residueValuation_eq_zero K x a).mp hz)

/-- Extension of the quotient valuation to its fraction field. -/
def fractionValuation (x : BanachSpectrum A) : Valuation (ResidueFraction x) ℝ≥0 :=
  (residueValuation K x).extendToLocalization
    (residueDenominators K x)
    (ResidueFraction x)

/-- The evaluation map into the algebraic residue field. -/
def fractionMap (x : BanachSpectrum A) : A →+* ResidueFraction x :=
  (algebraMap (ResidueDomain x) (ResidueFraction x)).comp (residueQuotient x)

@[simp]
theorem fractionValuation_map (x : BanachSpectrum A) (a : A) :
    (fractionValuation K x (fractionMap x a) : ℝ) = x a :=
  congrArg NNReal.toReal ((residueValuation K x).extendToLocalization_apply_map_apply
    (residueDenominators K x) (ResidueFraction x) (residueQuotient x a))

/-- The real absolute value on the actual residue fraction field. -/
def fractionAbsoluteValue (x : BanachSpectrum A) : AbsoluteValue (ResidueFraction x) ℝ where
  toFun a := fractionValuation K x a
  map_mul' a b := congrArg NNReal.toReal (map_mul (fractionValuation K x) a b)
  nonneg' _a := NNReal.coe_nonneg _
  eq_zero' _a := NNReal.coe_eq_zero.trans (Valuation.zero_iff _)
  add_le' a b := (show (fractionValuation K x (a + b) : ℝ) ≤
      max (fractionValuation K x a : ℝ) (fractionValuation K x b : ℝ) from
        (fractionValuation K x).map_add _ _).trans
      (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

/-- The residue fraction field with the norm derived from the spectrum point. -/
abbrev NormedResidueField (x : BanachSpectrum A) :=
  WithAbs (fractionAbsoluteValue K x)

/-- Evaluation in the residue field, retaining the point-dependent norm. -/
def residueFieldMap (x : BanachSpectrum A) : A →+* NormedResidueField K x :=
  (WithAbs.equiv (fractionAbsoluteValue K x)).symm.toRingHom.comp (fractionMap x)

@[simp]
theorem norm_residueFieldMap (x : BanachSpectrum A) (a : A) :
    ‖residueFieldMap K x a‖ = x a :=
  fractionValuation_map K x a

instance (x : BanachSpectrum A) : Algebra K (NormedResidueField K x) :=
  ((residueFieldMap K x).comp (algebraMap K A)).toAlgebra

@[simp]
theorem norm_residueField_algebraMap (x : BanachSpectrum A) (c : K) :
    ‖algebraMap K (NormedResidueField K x) c‖ = ‖c‖ :=
  (norm_residueFieldMap K x (algebraMap K A c)).trans (algebraMap_apply x c)

instance (x : BanachSpectrum A) : NormedAlgebra K (NormedResidueField K x) where
  norm_smul_le c a := by
    rw [Algebra.smul_def, norm_mul, norm_residueField_algebraMap]

instance (x : BanachSpectrum A) : IsUltrametricDist (NormedResidueField K x) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b =>
    (fractionValuation K x).map_add a.ofAbs b.ofAbs

/-- The completed residue field is the actual metric completion of the
kernel quotient's fraction field with its induced absolute value. -/
abbrev CompletedResidueField (x : BanachSpectrum A) :=
  UniformSpace.Completion (NormedResidueField K x)

instance (x : BanachSpectrum A) : IsUltrametricDist (CompletedResidueField K x) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro a b
  induction a, b using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
      simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using
        IsUltrametricDist.norm_add_le_max a b

/-- The canonical bounded algebra map from the Banach algebra to the
completed residue field, constructed by quotient, fraction field and completion. -/
def completedResidueMap (x : BanachSpectrum A) :
    BoundedAlgHom K A (CompletedResidueField K x) where
  toRingHom := UniformSpace.Completion.coeRingHom.comp (residueFieldMap K x)
  commutes' _ := rfl
  bounded := ⟨1, zero_lt_one, fun a => by
    change ‖(residueFieldMap K x a : CompletedResidueField K x)‖ ≤ 1 * ‖a‖
    rw [UniformSpace.Completion.norm_coe, norm_residueFieldMap, one_mul]
    exact x.le_norm a⟩

/-- The canonical inclusion of the normed residue fraction field into
its actual metric completion. -/
def residueCompletionMap (x : BanachSpectrum A) :
    NormedResidueField K x →+* CompletedResidueField K x :=
  UniformSpace.Completion.coeRingHom

end BanachSpectrum

end Langlands.Analytic
