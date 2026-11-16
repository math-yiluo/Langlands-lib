import Langlands.Global.RankinSelberg.EqualAnalyticResidue
import Langlands.Global.RankinSelberg.EqualAnalyticRegions
import Langlands.Global.RankinSelberg.UnequalAnalyticProof

/-! # Transpose inverse on `GL_n(F) \ GL_n(𝔸)` and Poisson summation at `g`

* `ι(g) = ᵗg⁻¹` preserves the quotient measure, so integrals of `GL_n(F)`-invariant functions
  satisfy `∫ f = ∫ f ∘ ι` (`lintegral_out_iota`, `integral_out_iota`).
* `ι(ζ(a)) = ζ(a⁻¹)` (`iota_zeta`).
* Poisson summation in the form used for the functional equation:
  `Θ(Φ, g) + Φ(0) = e^(-L(g)) (Θ(Φ̂, ι g) + Φ̂(0))` with `L(g) = log |det g|`
  (`thetaSum_poisson_points`).
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands Langlands.Global
open scoped CategoryTheory.MonObj Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

local instance dualSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F
local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

/-- **Transpose inverse preserves the quotient measure.** -/
theorem exists_iota_measurePreserving (n : ℕ) :
    ∃ jq : AdelicGroupPoints.RationalQuotient F (Scheme F n) ≃ᵐ
        AdelicGroupPoints.RationalQuotient F (Scheme F n),
      MeasurePreserving jq (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n))
        (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n)) ∧
      ∀ q, jq q = LeftCosetSpace.mk (glRational F n) (iota F n (Quotient.out q)) := by
  let Γ := glRational F n
  have hΓ := AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n)
  let α := UnequalAnalytic.iotaEquiv F n
  have hαΓ : ∀ x, α.toMulEquiv x ∈ Γ ↔ x ∈ Γ := by
    intro x
    change iota F n x ∈ Γ ↔ x ∈ Γ
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨_, (UnequalAnalytic.iota_rational F c).symm.trans
        (by rw [hc, UnequalAnalytic.iota_iota])⟩
    · rintro ⟨c, hc⟩
      exact ⟨_, (UnequalAnalytic.iota_rational F c).symm.trans (by rw [hc])⟩
  have hm1 : Measurable α.toMulEquiv := α.continuous.measurable
  have hm2 : Measurable α.toMulEquiv.symm := α.symm.continuous.measurable
  let jq := UnequalAnalytic.cosetMeasurableEquiv Γ α.toMulEquiv hαΓ hm1 hm2
  have hmap : Measure.map jq (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n)) =
      AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) := by
    have h1 : Measure.map jq (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n)) =
        ((mulEquivHaarChar α : ℝ≥0∞))⁻¹ •
          AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) :=
      UnequalAnalytic.map_cosetMap_discreteQuotientMeasure Γ hΓ α.toMulEquiv hαΓ hm1 hm2
        Measure.haar _ (UnequalAnalytic.map_haar_eq_smul α)
    rw [Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.mulEquivHaarChar_eq_one_of_involutive α
      (fun x => UnequalAnalytic.iota_iota F x), ENNReal.coe_one, inv_one, one_smul] at h1
    exact h1
  refine ⟨jq, ⟨jq.measurable, hmap⟩, fun q => ?_⟩
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

variable {F}

theorem iota_rational_mul_invariant {n : ℕ} {Z : Type*} {f : Points F n → Z}
    (hf : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      f (AdelicGroupPoints.rational F (Scheme F n) c * g) = f g)
    (c : RationalGroupPoints F (Scheme F n)) (g : Points F n) :
    f (iota F n (AdelicGroupPoints.rational F (Scheme F n) c * g)) = f (iota F n g) := by
  rw [UnequalAnalytic.iota_mul, UnequalAnalytic.iota_rational, hf]

theorem lift_out_eq {n : ℕ} {Z : Type*} {f : Points F n → Z}
    (hf : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      f (AdelicGroupPoints.rational F (Scheme F n) c * g) = f g) :
    ∃ hf' : ∀ (c : glRational F n) (g : Points F n), f ((c : Points F n) * g) = f g,
      (fun x : AdelicGroupPoints.RationalQuotient F (Scheme F n) => f (Quotient.out x)) =
        LeftCosetSpace.lift (glRational F n) f hf' := by
  have hf' : ∀ (c : glRational F n) (g : Points F n), f ((c : Points F n) * g) = f g := by
    rintro ⟨_, c, rfl⟩ g
    exact hf c g
  exact ⟨hf', funext fun x => (UnequalAnalytic.lift_eq_out _ f hf' x).symm⟩

theorem lintegral_out_iota {n : ℕ} {f : Points F n → ℝ≥0∞}
    (hf : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      f (AdelicGroupPoints.rational F (Scheme F n) c * g) = f g) :
    ∫⁻ x, f (Quotient.out x) ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      ∫⁻ x, f (iota F n (Quotient.out x))
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) := by
  obtain ⟨jq, hmp, hjq⟩ := exists_iota_measurePreserving F n
  obtain ⟨hf', hfun⟩ := lift_out_eq hf
  rw [hfun, ← hmp.lintegral_comp_emb jq.measurableEmbedding]
  refine lintegral_congr fun x => ?_
  rw [hjq, LeftCosetSpace.lift_mk]

theorem integral_out_iota {n : ℕ} {f : Points F n → ℂ}
    (hf : ∀ (c : RationalGroupPoints F (Scheme F n)) (g : Points F n),
      f (AdelicGroupPoints.rational F (Scheme F n) c * g) = f g) :
    ∫ x, f (Quotient.out x) ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) =
      ∫ x, f (iota F n (Quotient.out x))
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n) := by
  obtain ⟨jq, hmp, hjq⟩ := exists_iota_measurePreserving F n
  obtain ⟨hf', hfun⟩ := lift_out_eq hf
  rw [hfun, ← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show LeftCosetSpace.lift _ f hf' (jq x) = _
  rw [hjq, LeftCosetSpace.lift_mk]

theorem iota_zeta (n : ℕ) (a : Points F 1) : iota F n (zeta F n a) = zeta F n a⁻¹ := by
  apply (E n).injective
  rw [UnequalAnalytic.adelicEquiv_iota, adelicEquiv_zeta, adelicEquiv_zeta]
  apply Units.ext
  have hinv : ideleOf F a⁻¹ = (ideleOf F a)⁻¹ := by simp only [ideleOf, map_inv]
  rw [inverseTranspose_val, ← map_inv, hinv]
  change (Matrix.scalar (Fin n) (((ideleOf F a)⁻¹ : Ideles F) : Adeles F))ᵀ =
    Matrix.scalar (Fin n) (((ideleOf F a)⁻¹ : Ideles F) : Adeles F)
  rw [Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem log_detNorm_iota {n : ℕ} (g : Points F n) :
    Real.log (detNorm F n (iota F n g)) = -Real.log (detNorm F n g) := by
  rw [UnequalAnalytic.detNorm_iota, Real.log_inv]

variable [CompactSpace (AdeleQuotient F)]

/-- **Poisson summation at `g`.** -/
theorem thetaSum_poisson_points (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) (g : Points F n) :
    thetaSum F n Φ (E n g) + Φ 0 = Complex.exp (-(Real.log (detNorm F n g) : ℂ)) *
      (thetaSum F n (fourierTransform F n ψ Φ) (E n (iota F n g)) +
        fourierTransform F n ψ Φ 0) := by
  rw [thetaSum_poisson F n ψ hψ hΦ (E n g), UnequalAnalytic.adelicEquiv_iota]
  congr 1
  have h1 : absDet F n (E n g) = detNorm F n g := rfl
  rw [h1, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (UnequalAnalytic.detNorm_pos F g)]

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
