import Langlands.Global.AdelicLeviFibrePairingMajorants
import Langlands.Global.AdelicLeviFibrePairingKernel
import Langlands.Global.AdelicLeviPairingCompactFinite
import Langlands.Global.AdelicLeviFibreConstantTerm

/-! # The finite Iwasawa expansion in partial convolution form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "A₁" => normOneSubgroup F M
local notation "X₁" => NormOneRationalQuotient F M
local notation "dq₁" => normOneRationalQuotientHaarMeasure F M
local notation "jM" => fam.l J ≫ fam.p J
local notation "ι" => map F M G jM
local notation "ιU" => map F (fam.U J) G (fam.iU J ≫ fam.p J)
local notation "Γ" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)
local notation "Pos" => intrinsicSubgroup F T
local notation "pp" => positivePointMap F M T i
local notation "νP" => normalizedPositiveHaarMeasure F M T i hi I e hc
local notation "Q₊" => PositiveRationalQuotient F M T i
local notation "δ" => fam.leviModulus J
local notation "d" => (fun b : Pos => Complex.ofReal ((δ (pp b) : ℝ)⁻¹))

/-- The positive integrand in one summand of the finite Iwasawa expansion of a Levi pairing. -/
def leviFibrePairingExpansionIntegrand (β : C_c(A, ℂ)) (f : AM → ℂ) (t : Q₊ → ℂ) (g : A) (b : Pos) : ℂ :=
  (δ (pp b) : ℝ)⁻¹ • ∫ q : X₁,
    let y := ((Quotient.out q : A₁) : AM)
    f (pp b * y) *
      starRingEnd ℂ (normOnePartialConvolution T i (fam.leviFibrePairingKernel J T i β g b) t y) ∂dq₁

include hi e hc in
private theorem conj_normOnePartialConvolution_leviFibrePairingKernel (β : C_c(A, ℂ)) (g : A)
    (b : Pos) {t : AM → ℂ} (htc : Continuous t)
    (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t) (y : AM) :
    starRingEnd ℂ (normOnePartialConvolution T i (fam.leviFibrePairingKernel J T i β g b)
      (positiveQuotientOfNormOneRestriction T i hi I e hc htc hti) y) =
      ∫ x : A₁, fam.radicalKernel J β g 1 (pp b * ((x : AM)⁻¹ * y)) *
        starRingEnd ℂ (t x) ∂Measure.haar := by
  unfold normOnePartialConvolution
  rw [← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [map_mul, Complex.conj_conj, leviFibrePairingKernel_apply,
      positiveQuotientOfNormOneRestriction_mk])

include hi e hc in
/-- For a finite right compact expansion, the Levi pairing of the right convolution is
the integral of its finite expansion in the positive coordinate. -/
theorem exists_leviPairing_rightConvolution_eq_fibreExpansion
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (K : Subgroup A) (hK : IsIwasawaCompact (fam.p J) K) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (α : C_c(A, ℂ)) (φ : A → ℂ), Continuous φ →
      IsLeftInvariantUnder F G Γ φ → HasHeightGrowth rho φ →
      ∀ {n : ℕ} (k : Fin n → K) (a : Fin n → K → ℂ) (ha : ∀ j, Continuous (a j)),
      (∀ (x : K) (z : A), φ (z * x) = ∑ j, a j x * φ (z * k j)) →
      ∀ (t : AM → ℂ) (htc : Continuous t)
        (hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t),
      HasRapidDecayOnNormOneRepresentatives (jM ≫ rho) t → ∀ g : A,
        fam.leviPairing J (AdelicGroupPoints.rightConvolution F G α φ) g t =
          (c : ℝ) • ∑ j, ∫ b, fam.leviFibrePairingExpansionIntegrand J T i
            (compactRightAverageCc K hK.isCompact (a j) (ha j) α) (fam.leviFibre J φ (k j))
            (positiveQuotientOfNormOneRestriction T i hi I e hc htc hti) g b ∂νP := by
  obtain ⟨c, hc0, hIw⟩ := fam.leviPairing_rightConvolution_eq_iwasawa_finite J T i hi I e hc K hK
  refine ⟨c, hc0, fun α φ hφc hφi hφh n k a ha hdec t htc hti htd g => ?_⟩
  have hU (u : AdelicGroupPoints F (fam.U J)) (x : A) : φ (ιU u * x) = φ x :=
    hφi _ (Subgroup.mem_sup_left ⟨u, rfl⟩) _
  have hRat (r : RationalGroupPoints F M) (x : AM) : t (rational F M r * x) = t x :=
    hti _ ⟨r, rfl⟩ _
  rw [hIw α φ hφc hU (fam.leviRational_mul_of_parabolicInvariant J hφi) k a ha hdec
    t (htc.comp continuous_subtype_val) hRat g
    (fam.exists_leviPairing_iwasawa_majorant J rho hN hφh hφi hti htd K hK.isCompact)]
  refine congrArg ((c : ℝ) • ·) (Finset.sum_congr rfl fun j _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => congrArg ((δ (pp b) : ℝ)⁻¹ • ·) ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  let β := compactRightAverageCc K hK.isCompact (a j) (ha j) α
  let y : AM := (Quotient.out q : A₁)
  change φ (ι (pp b * y) * k j) * _ =
    φ (ι (pp b * y) * k j) *
      starRingEnd ℂ (normOnePartialConvolution T i (fam.leviFibrePairingKernel J T i β g b)
        (positiveQuotientOfNormOneRestriction T i hi I e hc htc hti) y)
  rw [fam.conj_normOnePartialConvolution_leviFibrePairingKernel J T i hi I e hc β g b htc hti]

include hi e hc in
/-- Changing the positive coordinate at a positive left translate yields the recentered
summand used in the Bochner vector formula. -/
theorem integral_leviFibrePairingExpansionIntegrand_mul_positive (β : C_c(A, ℂ))
    (f : AM → ℂ) (t : Q₊ → ℂ) (g : A) (a : Pos) :
    ∫ b, fam.leviFibrePairingExpansionIntegrand J T i β f t (ι (pp a) * g) b ∂νP =
      ∫ b, ∫ q : X₁, let y := ((Quotient.out q : A₁) : AM)
        d b * f (y * (pp a * pp b)) *
          starRingEnd ℂ (normOnePartialConvolution T i (fam.radicalKernelCc J β g 1) t (y * pp b))
        ∂dq₁ ∂νP := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveSecondCountableTopology F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F M T i hi I e hc
  conv_lhs => rw [← integral_mul_left_eq_self _ a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  unfold leviFibrePairingExpansionIntegrand
  dsimp only
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  let y : AM := (Quotient.out q : A₁)
  have hy : pp (a * b) * y = y * (pp a * pp b) := by
    rw [(positivePointMap_commute F M T i hc (a * b) y).eq, map_mul]
  have hδ : (δ (pp (a * b)) : ℝ) = (δ (pp a) : ℝ) * (δ (pp b) : ℝ) := by
    rw [map_mul, leviModulus_mul, NNReal.coe_mul]
  have hpos : (δ (pp a) : ℝ) ≠ 0 := (NNReal.coe_pos.mpr (fam.leviModulus_pos J (pp a))).ne'
  have hstar (z : ℂ) : starRingEnd ℂ ((δ (pp a) : ℝ) • z) = (δ (pp a) : ℝ) • starRingEnd ℂ z := by
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  dsimp only
  rw [fam.normOnePartialConvolution_leviFibrePairingKernel_mul_positive J T i hc, hstar, hy,
    ← mul_smul_comm, smul_smul, hδ, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hpos, mul_one,
    Complex.real_smul, mul_assoc]
  dsimp only [y]
  ring

end Langlands.Global.StandardParabolicFamily
