import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartRingEvaluation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartNormalization
import Langlands.Geometry.Analytic.RationalLocalization
import Langlands.Geometry.Analytic.AffinoidUnitNorm

/-! # Actual quotient maps to normalized strict rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) L))
  (g : StrictTateAlgebra (Fin n) L) (f : Fin m → StrictTateAlgebra (Fin n) L)

private theorem norm_adjoinVariables_le (p : StrictTateAlgebra (Fin n) L) :
    ‖WeierstrassPresentation.adjoinVariables L n m p‖ ≤ ‖p‖ :=
  evaluate_norm_le _ L _ _ (fun _ => (norm_X _ _ _).le) p

/-- The base map of a strict rational presentation is contractive. -/
theorem norm_baseMap_le (a : ofRelations L n S) :
    ‖baseMap L n m S g f a‖ ≤ ‖a‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p, hp, hpn⟩ := exists_representative_norm_lt L (ofRelations L n S) a hε
  change ‖(p : StrictTateAlgebra (Fin n) L)‖ < ‖a‖ + ε at hpn
  rw [← hp]
  change ‖presentationMap L (algebra L n m S g f)
    (WeierstrassPresentation.adjoinVariables L n m p)‖ ≤
      ‖presentationMap L (ofRelations L n S) p‖ + ε
  exact ((Ideal.Quotient.norm_mk_le _ _).trans (norm_adjoinVariables_le L n m p)).trans
    (by rw [hp]; exact hpn.le)

end RationalPresentation

namespace RationalLocalization

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (Q : PresentedStrictAffinoidAlgebra L) (m : ℕ) (g : Q) (f : Fin m → Q)

omit [CompleteSpace L] in
private theorem norm_equivOfEq_symm
    {P Q : PresentedStrictAffinoidAlgebra L} (h : P = Q) (a : Q) :
    ‖(equivOfEq L h).symm a‖ = ‖a‖ := by
  subst Q
  rfl

/-- The structural map to a strict rational quotient is contractive. -/
theorem norm_baseMap_le (a : Q) : ‖baseMap L Q m g f a‖ ≤ ‖a‖ := by
  exact (RationalPresentation.norm_baseMap_le L Q.arity m (Q.ideal : Set _)
    (seriesLift L Q g) (fun j => seriesLift L Q (f j))
    ((modelEquiv L Q).symm a)).trans_eq
      (norm_equivOfEq_symm L (ofRelations_ideal L Q) a)

/-- The actual strict fraction coordinates have quotient norm at most one. -/
theorem norm_fractionCoordinate_le (j : Fin m) :
    ‖fractionCoordinate L Q m g f j‖ ≤ 1 :=
  (Ideal.Quotient.norm_mk_le _ _).trans_eq (norm_X _ L _)

end RationalLocalization

namespace PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {L : Type v} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (d : RationalChart K A) (Q : PresentedStrictAffinoidAlgebra L)
  (ψ : BoundedRingHom A Q) (hψ : ∀ a, ‖ψ a‖ ≤ ‖a‖)
  (τ : Fin d.arity → L) (hτ : ∀ j, ‖τ j‖ = d.radii j)

omit [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
include hτ in
private theorem realizingScalar_ne_zero (j : Fin d.arity) : τ j ≠ 0 := by
  intro h
  have := hτ j
  rw [h, norm_zero] at this
  exact (d.radii.positive j).ne' this.symm

omit [IsUltrametricDist L] [CompleteSpace L] in
private theorem rescale_equation {B : Type v} [CommRing B] [Algebra L B]
    {t : L} (ht : t ≠ 0) {x y z : B}
    (h : x * z = algebraMap L B t⁻¹ * y) :
    x * (algebraMap L B t * z) = y := by
  calc
    _ = algebraMap L B t * (x * z) := by ring
    _ = algebraMap L B t * (algebraMap L B t⁻¹ * y) := by rw [h]
    _ = y := by rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]

/-- The original fraction expressed in the normalized strict quotient. -/
def normalizedStrictFraction (j : Fin d.arity) : (d.normalizedStrict Q ψ τ hτ).algebra :=
  (τ j) • RationalLocalization.fractionCoordinate L Q (d.normalizedStrict Q ψ τ hτ).arity
    (d.normalizedStrict Q ψ τ hτ).denominator
    (d.normalizedStrict Q ψ τ hτ).numerator j

omit [CompleteSpace K] in
theorem norm_normalizedStrictFraction_le (j : Fin d.arity) :
    ‖d.normalizedStrictFraction Q ψ τ hτ j‖ ≤ d.radii j := by
  change ‖τ j • RationalLocalization.fractionCoordinate L Q
    (d.normalizedStrict Q ψ τ hτ).arity
    (d.normalizedStrict Q ψ τ hτ).denominator
    (d.normalizedStrict Q ψ τ hτ).numerator j‖ ≤ _
  rw [norm_smul, hτ]
  exact mul_le_of_le_one_right (d.radii.positive j).le
    (RationalLocalization.norm_fractionCoordinate_le L Q _ _ _ j)

omit [CompleteSpace K] in
theorem normalizedStrictFraction_equation (j : Fin d.arity) :
    (d.normalizedStrict Q ψ τ hτ).baseMap (ψ (presentationMap K A d.denominator)) *
        d.normalizedStrictFraction Q ψ τ hτ j =
      (d.normalizedStrict Q ψ τ hτ).baseMap (ψ (presentationMap K A (d.numerators j))) := by
  unfold normalizedStrictFraction
  rw [Algebra.smul_def]
  apply rescale_equation (d.realizingScalar_ne_zero τ hτ j)
  have h := RationalLocalization.coordinate_equation L Q (d.normalizedStrict Q ψ τ hτ).arity
    (d.normalizedStrict Q ψ τ hτ).denominator
    (d.normalizedStrict Q ψ τ hτ).numerator j
  change (d.normalizedStrict Q ψ τ hτ).baseMap.toAlgHom
      (ψ (presentationMap K A d.denominator)) * _ =
    (d.normalizedStrict Q ψ τ hτ).baseMap.toAlgHom
      (algebraMap L Q (τ j)⁻¹ * ψ (presentationMap K A (d.numerators j))) at h
  rw [map_mul, AlgHom.commutes] at h
  exact h

/-- The contractive map from the actual weighted quotient to its normalized
strict quotient, over the supplied coefficient map. -/
def normalizedStrictMap :
    BoundedRingHom d.algebra (d.normalizedStrict Q ψ τ hτ).algebra :=
  d.ringEvaluate _ ((d.normalizedStrict Q ψ τ hτ).baseMap.toBoundedRingHom.comp ψ)
    (fun a => (RationalLocalization.norm_baseMap_le L Q _ _ _ (ψ a)).trans (hψ a))
    (d.normalizedStrictFraction Q ψ τ hτ)
    (d.norm_normalizedStrictFraction_le Q ψ τ hτ)
    (d.normalizedStrictFraction_equation Q ψ τ hτ)

@[simp] theorem normalizedStrictMap_baseMap (a : A) :
    d.normalizedStrictMap Q ψ hψ τ hτ (d.baseMap a) =
      (d.normalizedStrict Q ψ τ hτ).baseMap (ψ a) :=
  d.ringEvaluate_baseMap _ _ _ _ _ _ a

@[simp] theorem normalizedStrictMap_fraction (j : Fin d.arity) :
    d.normalizedStrictMap Q ψ hψ τ hτ
      (RationalPresentation.fraction K A d.radii d.denominator d.numerators j) =
        d.normalizedStrictFraction Q ψ τ hτ j :=
  d.ringEvaluate_fraction _ _ _ _ _ _ j

theorem norm_normalizedStrictMap_le (a : d.algebra) :
    ‖d.normalizedStrictMap Q ψ hψ τ hτ a‖ ≤ ‖a‖ :=
  d.norm_ringEvaluate_le _ _ _ _ _ _ a

end PresentedAffinoidAlgebra.RationalChart
end Langlands.Analytic
