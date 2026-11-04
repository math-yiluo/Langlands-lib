import Langlands.Representation.Plancherel.StandardIntertwiningIntegral
import Langlands.Analysis.Local.QuotientAutomorphismProof

/-! # The actual Levi transformation factor of the standard integral -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  (hMU' : M ≤ Subgroup.normalizer (U' : Set G))

include h in
omit [LocallyCompactSpace G] in
/-- Conjugation by the common Levi preserves the actual intersection inside
`U'`, without requiring that intersection to be normal in `U'`. -/
theorem intersection_conj_invariant (m : M) (u' : U') :
    HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩ u' ∈ U.subgroupOf U' ↔
      u' ∈ U.subgroupOf U' := by
  change (m : G) * (u' : G) * (m : G)⁻¹ ∈ U ↔ (u' : G) ∈ U
  exact (Subgroup.mem_normalizer_iff.mp (h.levi_le_normalizer m.property) u').symm

/-- The actual quotient homeomorphism `[u'] ↦ [m u' m⁻¹]`. -/
def quotientConjugation (m : M) :
    QuotientSpace (U := U) U' ≃ₜ QuotientSpace (U := U) U' :=
  QuotientIntegration.quotientAutomorphism (U.subgroupOf U')
    (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩)
    (intersection_conj_invariant h U' hMU' m)

omit [LocallyCompactSpace G] in
@[simp]
theorem quotientConjugation_symm_mk (m : M) (u' : U') :
    (quotientConjugation h U' hMU' m).symm (Quotient.mk _ u') =
      Quotient.mk _ ((HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩).symm u') := rfl

variable (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- Source Levi covariance becomes inverse conjugation on the quotient. -/
theorem integrand_levi_mul (m : M) (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (q : QuotientSpace (U := U) U') :
    integrand h hU U' A ((m : G) * g) f q =
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) •
        A.representation m
          (integrand h hU U' A g f ((quotientConjugation h U' hMU' m).symm q)) := by
  induction q using Quotient.inductionOn with
  | h u' =>
    simp only [quotientConjugation_symm_mk, integrand_mk]
    have hc := (leviInflated_covariant_iff h hU A
      (eval P (leviInflatedInducingRepresentation h hU A) f)).mp f.1.2 m (1 : U)
        ((m : G)⁻¹ * (u' : G) * (m : G) * g)
    simpa only [OneMemClass.coe_one, mul_one, HaarModulus.normalizerConj_symm_apply,
      mul_assoc, mul_inv_cancel_left] using hc

variable [LocallyCompactSpace U']
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]

/-- The actual inverse-conjugation integration factor: ambient target-radical
Haar modulus divided by intersection Haar modulus. -/
def quotientConjugationModulus (m : M) : ℝ≥0 :=
  letI : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  mulEquivHaarChar (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩) /
    mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism (U.subgroupOf U')
      (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩)
      (intersection_conj_invariant h U' hMU' m))

omit [LocallyCompactSpace G] in
/-- The change-of-variables factor is strictly positive. -/
theorem quotientConjugationModulus_pos (m : M) :
    0 < quotientConjugationModulus h hU U' hMU' m := by
  let : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  exact div_pos (mulEquivHaarChar_pos _) (mulEquivHaarChar_pos _)

section CompatibleMeasure

variable [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)

include hU hν

omit [LocallyCompactSpace G] [IsMulRightInvariant μU'] in
/-- The actual quotient conjugation scales a compatible measure by the
reciprocal of the inverse-conjugation factor. -/
theorem quotientConjugation_map (m : M) :
    Measure.map (quotientConjugation h U' hMU' m) ν =
      (((quotientConjugationModulus h hU U' hMU' m)⁻¹ : ℝ≥0) : ℝ≥0∞) • ν := by
  let : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  simpa only [quotientConjugation, quotientConjugationModulus, inv_div] using
    hν.map_quotientAutomorphism (U.subgroupOf U')
      (hU.preimage continuous_subtype_val)
      (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩)
      (intersection_conj_invariant h U' hMU' m)

omit [LocallyCompactSpace G] [IsMulRightInvariant μU'] in
/-- Inverse quotient conjugation preserves scalar absolute convergence. -/
theorem integrable_quotientConjugation_symm (m : M)
    (F : QuotientSpace (U := U) U' → ℂ) :
    MeasureTheory.Integrable
        (fun q => F ((quotientConjugation h U' hMU' m).symm q)) ν ↔
      MeasureTheory.Integrable F ν := by
  have hi := integrable_map_equiv (μ := ν)
    (quotientConjugation h U' hMU' m).toMeasurableEquiv
    (fun q => F ((quotientConjugation h U' hMU' m).symm q))
  change MeasureTheory.Integrable
      (fun q => F ((quotientConjugation h U' hMU' m).symm q))
      (Measure.map (quotientConjugation h U' hMU' m) ν) ↔
    MeasureTheory.Integrable
      (fun q => F ((quotientConjugation h U' hMU' m).symm
        (quotientConjugation h U' hMU' m q))) ν at hi
  simp only [Homeomorph.symm_apply_apply] at hi
  rw [quotientConjugation_map h hU U' hMU' ν μU' μI hν m] at hi
  have hc : (((quotientConjugationModulus h hU U' hMU' m)⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (inv_ne_zero
      (quotientConjugationModulus_pos h hU U' hMU' m).ne')
  exact (integrable_smul_measure hc ENNReal.coe_ne_top).symm.trans hi

omit [LocallyCompactSpace G] in
/-- Inverse quotient conjugation multiplies the genuine complex integral by
the actual ambient-to-intersection Haar modulus ratio. -/
theorem integral_quotientConjugation_symm (m : M)
    (F : QuotientSpace (U := U) U' → ℂ) :
    (∫ q, F ((quotientConjugation h U' hMU' m).symm q) ∂ν) =
      ((quotientConjugationModulus h hU U' hMU' m : ℝ) : ℂ) *
        ∫ q, F q ∂ν := by
  simpa only [quotientConjugation, quotientConjugationModulus] using
    (QuotientIntegration.compatibleQuotientAutomorphismScaling
      (U.subgroupOf U') (hU.preimage continuous_subtype_val) μU' μI ν hν
      (HaarModulus.normalizerConj U' ⟨m, hMU' m.property⟩)
      (intersection_conj_invariant h U' hMU' m)).2 F

/-- The scalar tests and representing vector transform by the actual Levi
action and the two proved Haar factors. -/
theorem weakIntegral_levi_mul (m : M) (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (v : A)
    (hv : HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation ν
      (integrand h hU U' A g f) v) :
    HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation ν
      (integrand h hU U' A ((m : G) * g) f)
      (((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
        ((quotientConjugationModulus h hU U' hMU' m : ℝ) : ℂ)) •
        A.representation m v) := by
  intro ℓ
  let ℓm : SmoothDual A.representation :=
    smoothContragredient A.representation m⁻¹ ℓ
  have hℓm (w : A) : ℓm.val w = ℓ.val (A.representation m w) := by
    change ℓ.val (A.representation (m⁻¹)⁻¹ w) = _
    rw [inv_inv]
  have hs : (fun q => ℓ.val (integrand h hU U' A ((m : G) * g) f q)) =
      fun q => (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
        ℓm.val (integrand h hU U' A g f
          ((quotientConjugation h U' hMU' m).symm q)) := by
    funext q
    rw [integrand_levi_mul h hU U' hMU' A, map_smul, hℓm]
    rfl
  rw [hs]
  have hi := (integrable_quotientConjugation_symm h hU U' hMU' ν μU' μI hν m
    (fun q => ℓm.val (integrand h hU U' A g f q))).mpr (hv ℓm).1
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul,
    integral_quotientConjugation_symm h hU U' hMU' ν μU' μI hν m
      (fun q => ℓm.val (integrand h hU U' A g f q)), (hv ℓm).2]
  simp only [map_smul, smul_eq_mul, hℓm, mul_assoc]

/-- On its actual domain the selected standard integral has the proved,
explicit Levi factor. No reductive modulus comparison is assumed. -/
theorem operator_levi_mul (hM : IsClosed (M : Set G))
    (f : domain h hU U' A ν) (m : M) (g : G) :
    operator h hU U' A ν hM f ((m : G) * g) =
      (((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
        ((quotientConjugationModulus h hU U' hMU' m : ℝ) : ℂ)) •
        A.representation m (operator h hU U' A ν hM f g)) := by
  exact ((operator_spec h hU U' A ν hM f) ((m : G) * g)).unique
    (compactCofinal hM) A.property
    (weakIntegral_levi_mul h hU U' hMU' A ν μU' μI hν m g f.val _
      ((operator_spec h hU U' A ν hM f) g))

end CompatibleMeasure

end Langlands.Plancherel.StandardIntertwining
