import Langlands.Representation.Classification.SegmentSpecialSquareIntegrabilityCriterionProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.SquareIntegrableCentralCharacterProof
import Langlands.Representation.Unitary.CentralCharacterProof
import Langlands.Representation.Twist.AdmissibilityProof

/-!
# Centered square-integrability of special quotients

The scalar character of an increasing segment quotient is the power of the
base scalar character times the determinant character at its midpoint.
The negative midpoint twist cancels that character exactly.
-/

noncomputable section

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-- Centering the supplied special quotient of a segment with unitarizable
supercuspidal base gives analytic square-integrability and an invariant positive
Hermitian form on the original carrier. -/
theorem segmentCenteredSpecialSquareIntegrability
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentCenteredSpecialSquareIntegrability.{uF, uV} F T := by
  let := T.topology
  intro Δ A hA hu π hπ
  have := T.generalLinearTopologicalGroup Δ.rank
  have := T.generalLinearTopologicalGroup Δ.degree
  obtain ⟨c⟩ := unitarizableCentralCharacter A.obj.representation
    A.property.2.1 A.property.1 hu
  let ω : F.Carrierˣ →* ℂˣ :=
    c.character.comp GeneralLinear.scalarToCenter
  have hω : HasScalarCharacter A.obj.representation GeneralLinear.scalar ω := by
    intro a v
    exact c.acts (GeneralLinear.scalarToCenter a) v
  have hωnorm : ∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ = 1 :=
    fun a => c.norm_eq_one (GeneralLinear.scalarToCenter a)
  let t : ℝ := ((Δ.length : ℝ) - 1) / 2
  let π₀ := π.twist (T.determinantPowerCharacter Δ.degree (-t))
    (T.isOpen_ker_determinantPowerCharacter Δ.degree (-t))
  have hi : Representation.IsIrreducible π.representation := hπ.choose_spec.2.1
  have hi₀ : Representation.IsIrreducible π₀.representation :=
    (isIrreducible_twist_iff _ _).mpr hi
  let := hi₀
  let : Nontrivial π₀ :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear Δ.degree F.Carrier)) π₀.representation.asModule
  have ha : IsAdmissible π.representation :=
    (CuspidalSupport.cuspidalEmbedding F T Δ.degree π hi).1
  have ha₀ : IsAdmissible π₀.representation :=
    (isAdmissible_twist_iff _ _
      (T.isOpen_ker_determinantPowerCharacter Δ.degree (-t))).mpr ha
  have hscalar := (segmentConstituentCentralCharacter.{uF, max uF uV}
    F T Δ ω A hA hω).2.2 π (Or.inr hπ)
  have hscalar₀ : HasScalarCharacter π₀.representation GeneralLinear.scalar
      (ω ^ Δ.length) := by
    have h := hasScalarCharacter_twist
      (T.determinantPowerCharacter Δ.degree (-t)) hscalar
    have he :
        (ω ^ Δ.length *
          (T.determinantPowerCharacter Δ.degree t).comp GeneralLinear.scalar) *
            (T.determinantPowerCharacter Δ.degree (-t)).comp GeneralLinear.scalar =
          ω ^ Δ.length := by
      ext a
      simp [PadicField.TopologicalData.determinantPowerCharacter,
        realPowerCharacter_neg, mul_assoc]
    rw [he] at h
    exact h
  have hnorm₀ : ∀ a : F.Carrierˣ, ‖((ω ^ Δ.length) a : ℂ)‖ = 1 := by
    intro a
    simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, norm_pow, hωnorm, one_pow]
  obtain ⟨c₀⟩ := (glSquareIntegrableCentralCharacter.{uF, max uF uV}
    p F T Δ.degree Δ.degree_pos π₀ π₀.representation (ω ^ Δ.length)
    ha₀ hscalar₀).2.1.mpr hnorm₀
  have hess₀ : T.IsEssentiallySquareIntegrable π₀.representation :=
    (segmentSpecialEssentialSquareIntegrability.{uF, uV} F T Δ π hπ).realPowerTwist (-t)
  have hsi₀ : T.IsSquareIntegrable π₀.representation :=
    isSquareIntegrable_of_essential_of_unitaryCentralCharacter T Δ.degree_pos hess₀ c₀
  exact ⟨hsi₀, glSquareIntegrableUnitarity.{uF, max uF uV}
    p F T Δ.degree Δ.degree_pos π₀ π₀.representation hi₀ hsi₀⟩

end Langlands.Classification
