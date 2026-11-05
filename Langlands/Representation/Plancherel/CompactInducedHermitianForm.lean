import Langlands.Representation.Aubert.General.NormalizedInductionUnitarity
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Plancherel.CompactCoefficientHaarComparison
import Langlands.Representation.Unitary.PositiveFormTensor

/-!
# Actual normalized induced forms with compact Haar probability

The compact probability is the existing measure of compact induction duality,
with its proved scalar integration law and equality with spherical Haar.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Plancherel.CompactInduction

open Aubert.General

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))

include hP hPK hG hδ in
/-- The actual induced Hermitian pairings satisfy the proved compact
probability integral law, with the full parabolic modulus. -/
theorem hermitianPairing_scalar
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A) (g : G) :
    Integrable (fun k : K =>
      b.inner (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g))
        (Induction.eval P (inducingRepresentation h hU A) j ((k : G) * g))) (measure K hK) ∧
    (∫ k : K,
      b.inner (Induction.eval P (inducingRepresentation h hU A) f ((k : G) * g))
        (Induction.eval P (inducingRepresentation h hU A) j ((k : G) * g))
        ∂measure K hK) =
      ∫ k : K, b.inner (Induction.eval P (inducingRepresentation h hU A) f k)
        (Induction.eval P (inducingRepresentation h hU A) j k) ∂measure K hK := by
  let : LocallyCompactSpace P := hP.locallyCompactSpace
  apply measure_scalar K hK hP hG hPK
    (fun x => b.inner (Induction.eval P (inducingRepresentation h hU A) f x)
      (Induction.eval P (inducingRepresentation h hU A) j x))
    (Induction.pairing_isLocallyConstant P _ b.toInnerProductCore f j)
  intro q x
  rw [normalizedInduction_pairing_covariant h hU A b f j q x, hδ q]

/-- The invariant positive form on actual normalized induction obtained using
exactly the existing compact Haar probability on the supplied `K`. -/
def invariantPositiveForm
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation) :
    InvariantPositiveForm ((normalizedInductionFunctor h hU).obj A).representation := by
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup (K : Subgroup G))
  let hmK : Measure.IsHaarMeasure (measure K hK) := measure_isHaar K hK
  let : (measure K hK).IsOpenPosMeasure := hmK.toIsOpenPosMeasure
  apply Induction.integralInvariantPositiveForm P (inducingRepresentation h hU A)
    b.toInnerProductCore (K : Subgroup G) (measure K hK)
  · intro g
    obtain ⟨q, hq, k, hk, he⟩ := hPK g
    exact ⟨⟨q, hq⟩, ⟨k, hk⟩, he⟩
  · intro f j
    change Integrable (fun k : K =>
      b.inner (Induction.eval P (inducingRepresentation h hU A) f k)
        (Induction.eval P (inducingRepresentation h hU A) j k)) (measure K hK)
    simpa only [mul_one] using
      (hermitianPairing_scalar h hU hP K hK hPK hG hδ A b f j 1).1
  · intro g f j
    exact (hermitianPairing_scalar h hU hP K hK hPK hG hδ A b f j g).2

/-- The form uses the exact same compact measure as the existing duality and
coefficient constructions. -/
theorem invariantPositiveForm_inner
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A) :
    (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner f j =
      ∫ k : K, b.inner (Induction.eval P (inducingRepresentation h hU A) f k)
        (Induction.eval P (inducingRepresentation h hU A) j k) ∂measure K hK := rfl

/-- This exact measure is also spherical Haar probability, with no unknown
scalar factor. -/
theorem invariantPositiveForm_inner_normalizedHaar
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)
    (f j : (normalizedInductionFunctor h hU).obj A) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    (invariantPositiveForm h hU hP K hK hPK hG hδ A b).inner f j =
      ∫ k : K, b.inner (Induction.eval P (inducingRepresentation h hU A) f k)
        (Induction.eval P (inducingRepresentation h hU A) j k)
        ∂HarishChandraSchwartz.normalizedHaar (K : Subgroup G) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [invariantPositiveForm_inner, measure_eq_normalizedHaar K hK]

/-- Positive rescaling commutes with the actual compact probability form. -/
theorem invariantPositiveForm_rescale
    (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)
    (a : ℝ) (ha : 0 < a) :
    invariantPositiveForm h hU hP K hK hPK hG hδ A (b.rescale a ha) =
      (invariantPositiveForm h hU hP K hK hPK hG hδ A b).rescale a ha := by
  apply InvariantPositiveForm.ext_inner
  intro f j
  rw [invariantPositiveForm_inner, InvariantPositiveForm.rescale_inner,
    invariantPositiveForm_inner]
  simp_rw [InvariantPositiveForm.rescale_inner]
  exact integral_const_mul _ _

/-- Actual pointwise induction transports the compact Haar form together with
the pulled-back inducing form, across independent carrier universes. -/
theorem invariantPositiveForm_ofEquiv
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (b : InvariantPositiveForm B.representation)
    (e : A.representation.Equiv B.representation) :
    invariantPositiveForm h hU hP K hK hPK hG hδ A (b.ofEquiv e) =
      (invariantPositiveForm h hU hP K hK hPK hG hδ B b).ofEquiv
        (normalizedInductionEquivOfEquiv h hU e) := by
  apply InvariantPositiveForm.ext_inner
  intro f j
  rw [invariantPositiveForm_inner]
  change _ = (invariantPositiveForm h hU hP K hK hPK hG hδ B b).inner
    (normalizedInductionEquivOfEquiv h hU e f) (normalizedInductionEquivOfEquiv h hU e j)
  rw [invariantPositiveForm_inner]
  rfl

end Langlands.Plancherel.CompactInduction
