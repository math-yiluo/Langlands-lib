import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCategory

/-! # Contractive ring evaluation of weighted rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K} (d : RationalChart K A)
  (B : Type v) [NormedCommRing B]
  (φ : BoundedRingHom A B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)

/-- The normed scalar action induced by a contractive coefficient ring map. -/
private abbrev coefficientNormedAlgebra : NormedAlgebra K B where
  __ := (φ.toRingHom.comp (algebraMap K A)).toAlgebra
  norm_smul_le c b := by
    change ‖φ (algebraMap K A c) * b‖ ≤ ‖c‖ * ‖b‖
    apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg b)
    apply (hφ _).trans
    rw [_root_.norm_algebraMap]
    exact mul_le_of_le_one_right (norm_nonneg c) (norm_one_le K A)

private abbrev coefficientAlgHom :
    letI := coefficientNormedAlgebra B φ hφ
    BoundedAlgHom K A B :=
  letI := coefficientNormedAlgebra B φ hφ
  { toRingHom := φ.toRingHom
    commutes' := fun _ => rfl
    bounded := φ.bounded }

variable [CompleteSpace K]

section Evaluation

variable [IsUltrametricDist B] [CompleteSpace B]
  (b : Fin d.arity → B) (hb : ∀ j, ‖b j‖ ≤ d.radii j)
  (hrel : ∀ j, φ (presentationMap K A d.denominator) * b j =
    φ (presentationMap K A (d.numerators j)))

omit [CompleteSpace K] [IsUltrametricDist B] [CompleteSpace B] in
include hφ in
private theorem norm_one_target_le : ‖(1 : B)‖ ≤ 1 := by
  simpa only [map_one] using (hφ 1).trans (norm_one_le K A)

private def ringEvaluationAlgHom :
    letI := coefficientNormedAlgebra B φ hφ
    BoundedAlgHom K d.algebra B := by
  letI := coefficientNormedAlgebra B φ hφ
  exact (RelativeRationalPresentation.evaluate K A d.radii
    (presentationMap K A d.denominator)
    (fun j => presentationMap K A (d.numerators j)) B
    (coefficientAlgHom B φ hφ) b hφ
    (monomialValue_norm_le_weight d.radii B (norm_one_target_le B φ hφ) b hb)
    hrel).comp
      (RationalPresentation.relativeEquiv K A d.radii d.denominator
        d.numerators).toBoundedAlgHom

/-- Evaluation into an arbitrary complete ultrametric ring. The scalar action on
the target is induced internally from the coefficient map. -/
def ringEvaluate : BoundedRingHom d.algebra B := by
  letI := coefficientNormedAlgebra B φ hφ
  exact (d.ringEvaluationAlgHom B φ hφ b hb hrel).toBoundedRingHom

@[simp] theorem ringEvaluate_baseMap (a : A) :
    d.ringEvaluate B φ hφ b hb hrel (d.baseMap a) = φ a := by
  let := coefficientNormedAlgebra B φ hφ
  change RelativeRationalPresentation.evaluate K A d.radii
    (presentationMap K A d.denominator)
    (fun j => presentationMap K A (d.numerators j)) B
    (coefficientAlgHom B φ hφ) b hφ
    (monomialValue_norm_le_weight d.radii B (norm_one_target_le B φ hφ) b hb)
    hrel (RationalPresentation.relativeEquiv K A d.radii d.denominator d.numerators
      (RationalPresentation.baseMap K A d.radii d.denominator d.numerators a)) = _
  rw [RationalPresentation.relativeEquiv_baseMap,
    RelativeRationalPresentation.evaluate_baseMap]
  rfl

@[simp] theorem ringEvaluate_fraction (j : Fin d.arity) :
    d.ringEvaluate B φ hφ b hb hrel
      (RationalPresentation.fraction K A d.radii d.denominator d.numerators j) = b j := by
  let := coefficientNormedAlgebra B φ hφ
  change RelativeRationalPresentation.evaluate K A d.radii
    (presentationMap K A d.denominator)
    (fun j => presentationMap K A (d.numerators j)) B
    (coefficientAlgHom B φ hφ) b hφ
    (monomialValue_norm_le_weight d.radii B (norm_one_target_le B φ hφ) b hb)
    hrel (RationalPresentation.relativeEquiv K A d.radii d.denominator d.numerators
      (RationalPresentation.fraction K A d.radii d.denominator d.numerators j)) = _
  rw [RationalPresentation.relativeEquiv_fraction,
    RelativeRationalPresentation.evaluate_fraction]

theorem norm_ringEvaluate_le (a : d.algebra) :
    ‖d.ringEvaluate B φ hφ b hb hrel a‖ ≤ ‖a‖ := by
  let := coefficientNormedAlgebra B φ hφ
  exact (RelativeRationalPresentation.norm_evaluate_le K A d.radii
    (presentationMap K A d.denominator)
    (fun j => presentationMap K A (d.numerators j)) B
    (coefficientAlgHom B φ hφ) b hφ
    (monomialValue_norm_le_weight d.radii B (norm_one_target_le B φ hφ) b hb)
    hrel _).trans_eq
      (RationalPresentation.norm_relativeEquiv K A d.radii d.denominator d.numerators a)

end Evaluation

omit [CompleteSpace K] in
include hφ in
/-- Bounded ring maps over one contractive coefficient map are unique.
Unit generation removes any need to prescribe the fraction images. -/
theorem ringHom_ext_over_base
    (ψ χ : BoundedRingHom d.algebra B)
    (hψ : ∀ a, ψ (d.baseMap a) = φ a)
    (hχ : ∀ a, χ (d.baseMap a) = φ a) : ψ = χ := by
  let := coefficientNormedAlgebra B φ hφ
  let ψ' : BoundedAlgHom K d.algebra B :=
    { toRingHom := ψ.toRingHom
      commutes' := fun c => by
        change ψ (algebraMap K d.algebra c) = φ (algebraMap K A c)
        rw [← d.baseMap.toAlgHom.commutes c]
        exact hψ _
      bounded := ψ.bounded }
  let χ' : BoundedAlgHom K d.algebra B :=
    { toRingHom := χ.toRingHom
      commutes' := fun c => by
        change χ (algebraMap K d.algebra c) = φ (algebraMap K A c)
        rw [← d.baseMap.toAlgHom.commutes c]
        exact hχ _
      bounded := χ.bounded }
  have h := RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators B
    d.generates ψ' χ' (BoundedAlgHom.ext fun a => (hψ a).trans (hχ a).symm)
  exact BoundedRingHom.ext fun a =>
    congrArg (fun f : BoundedAlgHom K d.algebra B => f a) h

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
