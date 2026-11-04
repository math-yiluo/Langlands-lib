import Langlands.Representation.Plancherel.StandardIntertwiningCovariance
import Langlands.Analysis.Local.SiegelSetMeasure

/-! # The standard integral as an actual target-normalized intertwiner -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

/-- The positive square-root consequence of the squared intersection identity. -/
theorem sqrt_mul_ratio_eq {a b c : ℝ≥0} (hc : c ≠ 0) (hsq : a * b = c ^ 2) :
    NNReal.sqrt a * (b / c) = NNReal.sqrt b := by
  have hs : NNReal.sqrt a * NNReal.sqrt b = c := by
    rw [← NNReal.sqrt_mul, hsq, NNReal.sqrt_sq]
  rw [← mul_div_assoc, div_eq_iff hc, ← hs]
  calc
    NNReal.sqrt a * b =
        NNReal.sqrt a * (NNReal.sqrt b * NNReal.sqrt b) := by
      rw [NNReal.mul_self_sqrt]
    _ = NNReal.sqrt b * (NNReal.sqrt a * NNReal.sqrt b) := by ring

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P P' M U U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]

/-- The remaining actual Haar-modulus identity. It is a premise for arbitrary
semidirect subgroup data, not a theorem supplied by this construction. -/
def SquaredModulusCompatibility : Prop :=
  letI : LocallyCompactSpace U' := hU'.locallyCompactSpace
  letI : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  ∀ m : M,
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m : ℝ≥0) *
      (HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m : ℝ≥0) =
    mulEquivHaarChar
      (QuotientIntegration.subgroupAutomorphism (U.subgroupOf U')
        (HaarModulus.normalizerConj U' ⟨m, h'.levi_le_normalizer m.property⟩)
        (intersection_conj_invariant h U' h'.levi_le_normalizer m)) ^ 2

/-- The proved quotient factor is exactly the positive target half-character
under the explicit squared modulus premise. -/
theorem leviFactor_eq_targetHalf
    (hsq : SquaredModulusCompatibility h hU h' hU') (m : M) :
    letI : LocallyCompactSpace U' := hU'.locallyCompactSpace
    (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) *
      ((quotientConjugationModulus h hU U' h'.levi_le_normalizer m : ℝ) : ℂ) =
        (HaarModulus.closedHalfCharacter U' hU' M h'.levi_le_normalizer m : ℂ) := by
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  let : LocallyCompactSpace (U.subgroupOf U') :=
    (hU.preimage (continuous_subtype_val : Continuous (Subtype.val : U' → G))).locallyCompactSpace
  have hb :
      (HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m : ℝ≥0) =
        mulEquivHaarChar
          (HaarModulus.normalizerConj U' ⟨m, h'.levi_le_normalizer m.property⟩) :=
    SiegelSetMeasure.mulEquivHaarChar_congr
      (@BorelSpace.mk U' _ (borel U') rfl) inferInstance _
  have he := sqrt_mul_ratio_eq
    (mulEquivHaarChar_pos
      (QuotientIntegration.subgroupAutomorphism (U.subgroupOf U')
        (HaarModulus.normalizerConj U' ⟨m, h'.levi_le_normalizer m.property⟩)
        (intersection_conj_invariant h U' h'.levi_le_normalizer m))).ne' (hsq m)
  rw [hb] at he
  change
    ((NNReal.sqrt
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m : ℝ≥0) : ℝ) : ℂ) *
      ((quotientConjugationModulus h hU U' h'.levi_le_normalizer m : ℝ) : ℂ) =
    ((NNReal.sqrt
      (HaarModulus.closedRestrictCharacter U' hU' M h'.levi_le_normalizer m : ℝ≥0) : ℝ) : ℂ)
  rw [hb]
  exact_mod_cast he

section CompatibleMeasure

variable [T2Space G]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (ν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
  (hM : IsClosed (M : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')

include hν hsq

/-- Every selected integral on the actual domain satisfies the target's full
positive Levi-normalized covariance law, conditionally on the modulus identity. -/
theorem operator_target_covariant (f : domain h hU U' A ν) :
    LeviNormalizedCovariant h' hU' A (operator h hU U' A ν hM f) := by
  let : LocallyCompactSpace U' := hU'.locallyCompactSpace
  intro m u' g
  rw [mul_assoc,
    operator_levi_mul h hU U' h'.levi_le_normalizer A ν μU' μI hν hM f,
    operator_unipotent_mul h hU U' A ν hM μU' μI hν,
    leviFactor_eq_targetHalf h hU h' hU' hsq]

/-- The actual integral packaged in the target positive Levi-normalized
smooth induction, on its original convergence and representability domain. -/
def targetOperator :
    domain h hU U' A ν →ₗ[ℂ]
      (DynamicNormalization.leviTwistedInductionFunctor h' hU').obj A where
  toFun f :=
    leviNormalizedFunctionOf h' hU' A (operator h hU U' A ν hM f)
      (operator_target_covariant h hU h' hU' A ν μU' μI hν hM hsq f)
      (Classical.choose (operator_uniformly_smooth h hU U' A ν hM f))
      (Classical.choose_spec (operator_uniformly_smooth h hU U' A ν hM f))
  map_add' f k := by
    apply Subtype.ext
    apply Subtype.ext
    exact (operator h hU U' A ν hM).map_add f k
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    exact (operator h hU U' A ν hM).map_smul c f

@[simp]
theorem targetOperator_eval (f : domain h hU U' A ν) (g : G) :
    eval P' (leviInflatedInducingRepresentation h' hU' A)
      (targetOperator h hU h' hU' A ν μU' μI hν hM hsq f) g =
        operator h hU U' A ν hM f g := rfl

/-- The target-valued map still represents the original scalar integrals. -/
theorem targetOperator_spec (f : domain h hU U' A ν) :
    HasIntegral h hU U' A ν f.val
      (eval P' (leviInflatedInducingRepresentation h' hU' A)
        (targetOperator h hU h' hU' A ν μU' μI hν hM hsq f)) :=
  operator_spec h hU U' A ν hM f

/-- The actual target-normalized standard integral intertwines the original
ambient actions on its actual domain. -/
def targetIntertwiner :
    (domainSubrepresentation h hU U' A ν).toRepresentation.IntertwiningMap
      ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj A).representation where
  toLinearMap := targetOperator h hU h' hU' A ν μU' μI hν hM hsq
  isIntertwining' t := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    exact operator_right_action h hU U' A ν hM f t

end CompatibleMeasure

end Langlands.Plancherel.StandardIntertwining
