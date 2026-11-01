import Langlands.Representation.Aubert.JacquetCompatibilityProof
import Langlands.Representation.Aubert.QuasicuspidalEigenvalue
import Langlands.Representation.Classification.SegmentJacquetReversal

/-! Actual reversed Jacquet classes of the unadjusted Aubert operator. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic CuspidalSupport
open OppositeCuspidalJacquetFiltration

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Upper Jacquet restriction for the reversed shape, transported back to the
original product Levi by actual inverse permutation conjugation. -/
def reversedJacquetObject {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) →
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) := by
  let := T.topology
  exact fun A => SmoothRep.pullback (outerReverseLeviEquivContinuous B F.Carrier)
    ((T.normalizedJacquetFunctor B.reverse).obj A)

/-- This actual transported Jacquet object has finite length whenever its
original general-linear representation does. -/
theorem reversedJacquetObject_hasFiniteLength {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → (reversedJacquetObject F T B A).HasFiniteLength := by
  let := T.topology
  intro A hA
  exact SmoothRep.pullbackFunctor_preservesFiniteLength
    (outerReverseLeviEquivContinuous B F.Carrier)
    ((T.normalizedJacquetFunctor B.reverse).obj A)
    (normalizedJacquetK0_hasFiniteLength F T B.reverse A hA)

/-- The transported action is literally the reversed upper Jacquet action
pulled back by reversal of the product-Levi labels. -/
theorem reversedJacquetObject_representation {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      (reversedJacquetObject F T B A).representation =
        (((T.normalizedJacquetFunctor B.reverse).obj A).representation.comp
          (leviReverseEquiv B).toMonoidHom) := by
  let := T.topology
  intro A
  rfl

/-- If the actual reversed upper Jacquet module is quasicuspidal, its
transported exact class computes the upper Jacquet class of the Aubert image. -/
def QuasicuspidalJacquetExchangeStatement : Prop := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact ∀ (n : ℕ) (B : BlockShape n)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hA : A.HasFiniteLength),
    IsLeviQuasicuspidal B.reverse
      ((T.normalizedJacquetFunctor B.reverse).obj A).representation →
    normalizedJacquetK0.{uF, uV} F T B
        (alternatingOperator.{uF, uV} F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA)) =
      ((-1 : ℤ) ^ (n - B.length)) •
        B.finiteLengthClass F.Carrier (reversedJacquetObject F T B A)
          (reversedJacquetObject_hasFiniteLength F T B A hA)

theorem quasicuspidalJacquetExchange :
    QuasicuspidalJacquetExchangeStatement.{uF, uV} F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n B A hA hqc
  have hJ := normalizedJacquetK0_hasFiniteLength F T B.reverse A hA
  have h := LinearMap.congr_fun (jacquetCompatibility.{uF, uV} F T n B)
    (GeneralLinear.finiteLengthClass n F.Carrier A hA)
  change normalizedJacquetK0 F T B
      (alternatingOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA)) =
    leviTransportK0 F.Carrier B.reverse B B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B)
      (alternatingOperatorOnLevi F T B.reverse
        (normalizedJacquetK0 F T B.reverse
          (GeneralLinear.finiteLengthClass n F.Carrier A hA))) at h
  rw [normalizedJacquetK0_finiteLengthClass F T B.reverse A hA hJ,
    alternatingOperatorOnLevi_quasicuspidal F T B.reverse _ hJ hqc, map_smul,
    leviTransportK0, leviConjugationContinuous_outerReverse_symm] at h
  change normalizedJacquetK0 F T B
      (alternatingOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA)) =
    ((-1 : ℤ) ^ (n - B.length)) •
      SmoothRep.FiniteLengthGrothendieckGroup.pullback
        (outerReverseLeviEquivContinuous B F.Carrier)
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
          ((T.normalizedJacquetFunctor B.reverse).obj A) hJ) at h
  rw [SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation _ _ hJ
    (reversedJacquetObject_hasFiniteLength F T B A hA)] at h
  exact h

private theorem normalizedJacquetObject_heq_of_shape_eq {n : ℕ}
    {B C : BlockShape n} (h : B = C) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      HEq ((T.normalizedJacquetFunctor B).obj A)
        ((T.normalizedJacquetFunctor C).obj A) := by
  cases h
  intro A
  rfl

section Uniform

variable {m r : ℕ} (hr : 0 < r)

/-- Reversal preserves the uniform shape and its actual Jacquet object. -/
theorem uniformJacquetObject_reverse_eq
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier)) :
    letI := T.topology
    (T.normalizedJacquetFunctor (BlockShape.uniform m r hr).reverse).obj π =
      (T.normalizedJacquetFunctor (BlockShape.uniform m r hr)).obj π := by
  let := T.topology
  exact eq_of_heq (normalizedJacquetObject_heq_of_shape_eq F T
    (show (BlockShape.uniform m r hr).reverse = BlockShape.uniform m r hr from rfl) π)

private theorem intertwiner_equiv_comp_ne_zero
    {G U V W : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G U} {σ : Representation ℂ G V}
    {τ : Representation ℂ G W}
    (e : σ.Equiv τ) (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    e.toIntertwiningMap.comp f ≠ 0 := by
  intro h
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun k => k v) h
  have he : e (f v) = 0 := hv
  exact e.toLinearEquiv.injective (he.trans e.toLinearEquiv.map_zero.symm)

/-- Actual conjugation transport of the increasing tensor for equal-sized
blocks is equivalent to the decreasing tensor. -/
def segmentTensorTransportReverseEquiv
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    let B := BlockShape.uniform m r hr
    (transport B.reverse B B.reversePermutation
      (conjugatesLevi_reversePermutation F.Carrier B)
      (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation).Equiv
        (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A m hr)).representation := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  have he :
      transport B.reverse B B.reversePermutation
          (conjugatesLevi_reversePermutation F.Carrier B)
          (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation =
        ((FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation.comp
          (leviReverseEquiv B).toMonoidHom) := by
    apply MonoidHom.ext
    intro g
    change (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation
      ((leviConjugation B.reverse B B.reversePermutation
        (conjugatesLevi_reversePermutation F.Carrier B)).symm g) = _
    rw [leviConjugation_outerReverse_symm]
    rfl
  exact (Langlands.equivOfRepresentationEq he).trans
    (Classification.segmentTensorReverseEquiv T m hr A)

/-- Uniform product-label pullback turns a nonzero map to the increasing
tensor into a nonzero map to the decreasing tensor. -/
theorem exists_pullback_to_segmentTensorDown_ne_zero
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (J : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ ((BlockShape.uniform m r hr).Levi F.Carrier))
    (f : letI := T.topology
      J.representation.IntertwiningMap
        (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation)
    (hf : f ≠ 0) :
    letI := T.topology
    ∃ g : (SmoothRep.pullback
        (outerReverseLeviEquivContinuous (BlockShape.uniform m r hr) F.Carrier) J).representation.IntertwiningMap
        (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A m hr)).representation,
      g ≠ 0 := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  let f' : Representation.IntertwiningMap
      (J.representation.comp
        (leviReverseEquiv B).toMonoidHom)
      ((FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation.comp
        (leviReverseEquiv B).toMonoidHom) :=
    ⟨f.toLinearMap, fun g => f.isIntertwining' (leviReverseEquiv B g)⟩
  let e := Classification.segmentTensorReverseEquiv T m hr A
  have hf' : f' ≠ 0 := by
    intro h
    have hlin : f'.toLinearMap = 0 :=
      congrArg (fun k => k.toLinearMap) h
    exact hf (Representation.IntertwiningMap.ext hlin)
  exact ⟨e.toIntertwiningMap.comp f', intertwiner_equiv_comp_ne_zero e f' hf'⟩

/-- A nonzero map from the full uniform upper Jacquet module to the increasing
tensor gives a nonzero map from the actual transported Jacquet object to the
decreasing tensor. No irreducibility or finite-length assumption is needed. -/
theorem exists_reversedJacquet_to_segmentTensorDown_ne_zero
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
    (f : letI := T.topology
      ((T.normalizedJacquetFunctor (BlockShape.uniform m r hr)).obj π).representation.IntertwiningMap
        (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)).representation)
    (hf : f ≠ 0) :
    letI := T.topology
    ∃ g : (reversedJacquetObject F T (BlockShape.uniform m r hr) π).representation.IntertwiningMap
        (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A m hr)).representation,
      g ≠ 0 := by
  let := T.topology
  change ∃ g : (SmoothRep.pullback
      (outerReverseLeviEquivContinuous (BlockShape.uniform m r hr) F.Carrier)
      ((T.normalizedJacquetFunctor (BlockShape.uniform m r hr).reverse).obj π)).representation.IntertwiningMap
        (FiniteTensor.externalSmoothObject (T.segmentFactorsDown A m hr)).representation, g ≠ 0
  rw [uniformJacquetObject_reverse_eq F T hr π]
  exact exists_pullback_to_segmentTensorDown_ne_zero F T hr A _ f hf

end Uniform

end Langlands.Aubert
