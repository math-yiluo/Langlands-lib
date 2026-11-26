import Langlands.Global.AdelicCuspidalAnnihilator
import Langlands.Global.AdelicLocalFinitenessStatement
import Mathlib.MeasureTheory.Integral.Prod

/-! # Right convolution and the norm-one cuspidal pairings -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.StandardParabolicFamily

open AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "A₁" => normOneSubgroup F M
local notation "Γ" => rationalNormOneSubgroup F M
local notation "Q" => NormOneRationalQuotient F M
local notation "ι" => AdelicGroupPoints.map F M G (fam.l J ≫ fam.p J)
local notation "dM" => normOneRationalQuotientHaarMeasure F M
local notation "dg" => (Measure.haar : Measure A)

/-- One integrable function of the norm-one Levi class bounds the pairing integrands
at all points in the indicated set of right translations. -/
def HasCompactLeviPairingMajorant (f : A → ℂ) (ψ : AdelicGroupPoints F M → ℂ)
    (g : A) (C : Set A) : Prop :=
  ∃ b : Q → ℝ, Integrable b dM ∧
    ∀ᵐ q ∂dM, ∀ t ∈ C, ‖fam.leviPairingIntegrand J f (g * t) ψ q‖ ≤ b q

/-- Rational invariance identifies the descended integrand with its evaluation on any
norm-one Levi representative. -/
theorem leviPairingIntegrand_mk_of_leviInvariant
    {f : A → ℂ} {ψ : AdelicGroupPoints F M → ℂ}
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    (hψ : IsLeftInvariantUnder F M (rationalSubgroup F M) ψ)
    (g : A) (x : A₁) :
    fam.leviPairingIntegrand J f g ψ (LeftCosetSpace.mk Γ x) =
      f (ι x.val * g) * starRingEnd ℂ (ψ x.val) := by
  let b (y : A₁) := f (ι y.val * g) * starRingEnd ℂ (ψ y.val)
  have hb (r : Γ) (y : A₁) : b (r.val * y) = b y := by
    obtain ⟨v, hv⟩ := r.property
    have heq : rational F M v = r.val.val := congrArg Subtype.val hv
    change f (ι (r.val.val * y.val) * g) * starRingEnd ℂ (ψ (r.val.val * y.val)) = _
    rw [map_mul, mul_assoc, ← heq, hf, hψ (rational F M v) ⟨v, rfl⟩]
  let B := LeftCosetSpace.lift Γ b hb
  change b (Quotient.out (LeftCosetSpace.mk Γ x)) = b x
  exact congrArg B (Quotient.out_eq (LeftCosetSpace.mk Γ x))

private theorem continuous_leviPairingIntegrand_at_rightTranslate
    {f : A → ℂ} {ψ : AdelicGroupPoints F M → ℂ} (hfc : Continuous f) (hψc : Continuous ψ)
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    (hψ : IsLeftInvariantUnder F M (rationalSubgroup F M) ψ) (g : A) :
    Continuous (fun z : Q × A => fam.leviPairingIntegrand J f (g * z.2) ψ z.1) := by
  rw [← ((LeftCosetSpace.isOpenQuotientMap_mk Γ).prodMap
    (IsOpenQuotientMap.id (X := A))).continuous_comp_iff]
  change Continuous (fun z : A₁ × A =>
    fam.leviPairingIntegrand J f (g * z.2) ψ (LeftCosetSpace.mk Γ z.1))
  simp_rw [fam.leviPairingIntegrand_mk_of_leviInvariant J hf hψ]
  exact (hfc.comp (((ι).continuous.comp (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_const.mul continuous_snd))).mul
    (hψc.comp (continuous_subtype_val.comp continuous_fst)).star

/-- With an integrable majorant uniform over the kernel support, pairing a compact
right convolution can be computed by convolving the scalar pairings. -/
theorem leviPairing_rightConvolution_of_compactMajorant
    {h f : A → ℂ} {ψ : AdelicGroupPoints F M → ℂ}
    (hh : Continuous h) (hcomp : HasCompactSupport h) (hfc : Continuous f) (hψc : Continuous ψ)
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    (hψ : IsLeftInvariantUnder F M (rationalSubgroup F M) ψ)
    (g : A) (hbound : fam.HasCompactLeviPairingMajorant J f ψ g (tsupport h)) :
    Integrable (fam.leviPairingIntegrand J (rightConvolution F G h f) g ψ) dM ∧
      fam.leviPairing J (rightConvolution F G h f) g ψ =
        rightConvolution F G h (fun x => fam.leviPairing J f x ψ) g := by
  let ν := (dg).restrict (tsupport h)
  have hC := hcomp.isCompact
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  let P (q : Q) (t : A) := h t * fam.leviPairingIntegrand J f (g * t) ψ q
  have hP : Continuous (Function.uncurry P) := (hh.comp continuous_snd).mul
    (fam.continuous_leviPairingIntegrand_at_rightTranslate J hfc hψc hf hψ g)
  obtain ⟨b, hb, hdom⟩ := hbound
  let β := hb.aestronglyMeasurable.mk b
  have hβ : StronglyMeasurable β := hb.aestronglyMeasurable.stronglyMeasurable_mk
  have hbβ : b =ᵐ[dM] β := hb.aestronglyMeasurable.ae_eq_mk
  have hβi : Integrable β dM := hb.congr hbβ
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn hh.continuousOn
  let B := max 0 R
  have hB : 0 ≤ B := le_max_left _ _
  let majorant (z : Q × A) := B * β z.1
  have hMi : Integrable majorant ((dM).prod ν) := (hβi.const_mul B).comp_fst ν
  have hM : Measurable majorant := measurable_const.mul (hβ.measurable.comp measurable_fst)
  have hPdom : ∀ᵐ z ∂(dM).prod ν, ‖Function.uncurry P z‖ ≤ majorant z := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hP.norm.measurable hM)).2
    filter_upwards [hdom, hbβ] with q hq hqβ
    filter_upwards [ae_restrict_mem hC.isClosed.measurableSet] with t ht
    have hqt : ‖fam.leviPairingIntegrand J f (g * t) ψ q‖ ≤ β q := hqβ ▸ hq t ht
    change ‖h t * fam.leviPairingIntegrand J f (g * t) ψ q‖ ≤ B * β q
    rw [norm_mul]
    exact mul_le_mul ((hR t ht).trans (le_max_right _ _)) hqt (norm_nonneg _) hB
  have hI : Integrable (Function.uncurry P) ((dM).prod ν) := hMi.mono' hP.aestronglyMeasurable hPdom
  have hout (q : Q) : (∫ t, P q t ∂ν) =
      fam.leviPairingIntegrand J (rightConvolution F G h f) g ψ q := by
    have hAll : (∫ t, P q t ∂ν) = ∫ t, P q t ∂dg := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      simp only [P, image_eq_zero_of_notMem_tsupport ht, zero_mul]
    rw [hAll]
    simp only [P, leviPairingIntegrand]
    simp_rw [← mul_assoc, integral_mul_const, rightConvolution]
  refine ⟨?_, ?_⟩
  · exact hI.integral_prod_left.congr (Filter.Eventually.of_forall hout)
  · unfold leviPairing at *
    simp_rw [← hout]
    rw [integral_integral_swap hI]
    unfold rightConvolution
    simp_rw [P, integral_const_mul]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp only [image_eq_zero_of_notMem_tsupport ht, zero_mul]

/-- Compactly supported right convolution preserves the cuspidal annihilator provided its
test pairings admit integrable majorants on the support of the kernel. -/
theorem InCuspidalAnnihilator.rightConvolution_of_compactMajorants
    {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {h f : A → ℂ} (hh : Continuous h) (hcomp : HasCompactSupport h) (hfc : Continuous f)
    (hf : ∀ (r : RationalGroupPoints F M) (x : A), f (ι (rational F M r) * x) = f x)
    (hkill : fam.InCuspidalAnnihilator Kinf rho J f)
    (hMajorants : ∀ ψ, fam.IsLeviCuspForm Kinf rho J ψ →
      ∀ g, fam.HasCompactLeviPairingMajorant J f ψ g (tsupport h)) :
    fam.InCuspidalAnnihilator Kinf rho J (rightConvolution F G h f) := by
  intro ψ hψ g
  obtain ⟨hI, heq⟩ := fam.leviPairing_rightConvolution_of_compactMajorant J hh hcomp hfc
    hψ.1.2.1.1 hf hψ.1.1 g (hMajorants ψ hψ g)
  refine ⟨hI, ?_⟩
  rw [heq]
  unfold rightConvolution
  simp only [fun t => (hkill ψ hψ t).2, mul_zero, integral_zero]

end Langlands.Global.StandardParabolicFamily
