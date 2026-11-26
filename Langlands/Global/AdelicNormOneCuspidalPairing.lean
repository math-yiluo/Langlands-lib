import Langlands.Global.AdelicNormOneCuspidalSeparationStatement
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicLocalFinitenessStatement
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-! # Pairing on the norm-one quotient and compact right convolution -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local notation "A" => AdelicGroupPoints F G
local notation "S₁" => normOneSubgroup F G
local notation "Q" => NormOneRationalQuotient F G
local notation "Γ" => rationalNormOneSubgroup F G
local notation "ν" => normOneRationalQuotientHaarMeasure F G
local notation "dg" => (Measure.haar : Measure A)
local notation "J" => normOneCuspidalPairingIntegrand

/-- Restrict an ambient function to the selected representatives of the
norm-one rational quotient. For invariant functions this is the descent. -/
def normOneRationalRestriction (f : A → ℂ) (q : Q) : ℂ := f (Quotient.out q : S₁).val

private theorem normOneRationalRestriction_invariant {f : A → ℂ}
    (hf : IsLeftInvariantUnder F G (rationalSubgroup F G) f) (r : Γ) (x : S₁) :
    f ((r.val * x).val) = f x.val := by
  obtain ⟨q, hq⟩ := r.2
  exact hf r.val.val ⟨q, congrArg Subtype.val hq⟩ x.val

private theorem normOneRationalRestriction_eq_lift {f : A → ℂ}
    (hf : IsLeftInvariantUnder F G (rationalSubgroup F G) f) :
    normOneRationalRestriction f =
      LeftCosetSpace.lift Γ (fun x => f x.val) (normOneRationalRestriction_invariant hf) := by
  let lifted := LeftCosetSpace.lift Γ (fun x => f x.val) (normOneRationalRestriction_invariant hf)
  funext q
  change lifted (LeftCosetSpace.mk Γ (Quotient.out q)) = lifted q
  exact congrArg lifted (Quotient.out_eq q)

@[simp]
theorem normOneRationalRestriction_mk {f : A → ℂ}
    (hf : IsLeftInvariantUnder F G (rationalSubgroup F G) f) (x : S₁) :
    normOneRationalRestriction f (LeftCosetSpace.mk Γ x) = f x.val := by
  rw [normOneRationalRestriction_eq_lift hf, LeftCosetSpace.lift_mk]

theorem continuous_normOneRationalRestriction {f : A → ℂ} (hf : Continuous f)
    (hfInv : IsLeftInvariantUnder F G (rationalSubgroup F G) f) :
    Continuous (normOneRationalRestriction f) := by
  rw [normOneRationalRestriction_eq_lift hfInv]
  exact LeftCosetSpace.continuous_lift Γ _ _ (hf.comp continuous_subtype_val)

theorem normOneCuspidalPairingIntegrand_mk {f ψ : A → ℂ}
    (hf : IsLeftInvariantUnder F G (rationalSubgroup F G) f)
    (hψ : IsLeftInvariantUnder F G (rationalSubgroup F G) ψ) (a : A) (x : S₁) :
    J f ψ a (LeftCosetSpace.mk Γ x) = f (x.val * a) * starRingEnd ℂ (ψ x.val) := by
  have hf' : IsLeftInvariantUnder F G (rationalSubgroup F G) (fun z => f (z * a)) := by
    intro r hr z
    change f ((r * z) * a) = f (z * a)
    rw [mul_assoc, hf r hr]
  change normOneRationalRestriction (fun z => f (z * a)) (LeftCosetSpace.mk Γ x) *
    starRingEnd ℂ (normOneRationalRestriction ψ (LeftCosetSpace.mk Γ x)) = _
  rw [normOneRationalRestriction_mk hf', normOneRationalRestriction_mk hψ]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A bound along representatives of all rational orbits on the norm-one
quotient puts the invariant continuous function in `Lᵖ` for every `p`. -/
theorem memLp_normOneRationalRestriction (hG : IsConnectedReductive G)
    {S : Set A} (hS : ∀ x : S₁, ∃ q : RationalGroupPoints F G, rational F G q * x.val ∈ S)
    {f : A → ℂ} (hf : Continuous f) (hfInv : IsLeftInvariantUnder F G (rationalSubgroup F G) f)
    {C : ℝ} (hC : ∀ x ∈ S, ‖f x‖ ≤ C) (p : ℝ≥0∞) :
    MemLp (normOneRationalRestriction f) p ν := by
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F G hG
  apply MemLp.of_bound (continuous_normOneRationalRestriction hf hfInv).aestronglyMeasurable C
  refine Filter.Eventually.of_forall fun z => ?_
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ z
  obtain ⟨q, hq⟩ := hS x
  rw [normOneRationalRestriction_mk hfInv, ← hfInv _ ⟨q, rfl⟩ x.val]
  exact hC _ hq

variable {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "H" => adelicHeight F G rho

/-- Uniform rapid decay of the test on orbit representatives makes the
pairing compatible with compact right convolution of a moderate input. -/
def AdelicNormOneCuspidalPairingStatement : Prop :=
  IsConnectedReductive G → 0 < N →
  ∀ (S : Set A), (∀ x : S₁, ∃ q : RationalGroupPoints F G, rational F G q * x.val ∈ S) →
  ∀ (f ψ h : A → ℂ), Continuous f → Continuous ψ → Continuous h → HasCompactSupport h →
    IsLeftInvariantUnder F G (rationalSubgroup F G) f →
    IsLeftInvariantUnder F G (rationalSubgroup F G) ψ →
    HasModerateGrowthFunction F G rho f →
    (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ‖ψ x‖ * H x ^ m ≤ C) →
    Integrable (J (rightConvolution F G h f) ψ 1) ν ∧
      (∫ x, J (rightConvolution F G h f) ψ 1 x ∂ν) =
        ∫ a, h a * (∫ x, J f ψ a x ∂ν) ∂dg

theorem adelicNormOneCuspidalPairing_rightConvolution : AdelicNormOneCuspidalPairingStatement rho := by
  intro hG hN S hS f ψ h hf hψ hh hhSupp hfInv hψInv hGrow hDecay
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F G hG
  obtain ⟨Cf, r, hCf, hr, hBnd⟩ := (hasModerateGrowthFunction_iff_hasHeightGrowth hN f).mp hGrow
  obtain ⟨m, hm⟩ := exists_nat_ge r
  obtain ⟨Cψ, hCψ, hDec⟩ := hDecay m
  obtain ⟨B, hB⟩ := (hhSupp.image (continuous_adelicHeight F G rho hN)).bddAbove
  let D := max 1 B
  have hD : 0 ≤ D := zero_le_one.trans (le_max_left _ _)
  have hH (x : A) : 1 ≤ H x := one_le_adelicHeight F G rho hN x
  have hH₀ (x : A) : 0 ≤ H x := zero_le_one.trans (hH x)
  have hProd (z : A) (hz : z ∈ S) (a : A) (ha : a ∈ tsupport h) :
      ‖f (z * a)‖ * ‖ψ z‖ ≤ Cf * D ^ r * Cψ := by
    have hHa : H a ≤ D := (hB ⟨a, ha, rfl⟩).trans (le_max_right _ _)
    have hHza : H (z * a) ≤ D * H z := by
      rw [mul_comm D]
      exact (adelicHeight_mul_le F G rho hN z a).trans (mul_le_mul_of_nonneg_left hHa (hH₀ z))
    have hP : H z ^ r ≤ H z ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (hH z) hm
    calc
      ‖f (z * a)‖ * ‖ψ z‖ ≤ Cf * H (z * a) ^ r * ‖ψ z‖ :=
        mul_le_mul_of_nonneg_right (hBnd _) (norm_nonneg _)
      _ ≤ Cf * (D * H z) ^ r * ‖ψ z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hH₀ _) hHza hr) hCf) (norm_nonneg _)
      _ = Cf * D ^ r * (‖ψ z‖ * H z ^ r) := by rw [Real.mul_rpow hD (hH₀ z)]; ring
      _ ≤ Cf * D ^ r * (‖ψ z‖ * H z ^ m) := by gcongr
      _ ≤ Cf * D ^ r * Cψ := by gcongr; exact hDec z hz
  let P (p : Q × A) : ℂ := h p.2 * J f ψ p.2 p.1
  have hPCont : Continuous P := by
    rw [← ((LeftCosetSpace.isOpenQuotientMap_mk Γ).prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    have he : ∀ p : S₁ × A, P (LeftCosetSpace.mk Γ p.1, p.2) =
        h p.2 * (f (p.1.val * p.2) * starRingEnd ℂ (ψ p.1.val)) := by
      intro p
      exact congrArg (h p.2 * ·) (normOneCuspidalPairingIntegrand_mk hfInv hψInv p.2 p.1)
    exact ((hh.comp continuous_snd).mul
      ((hf.comp ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).mul
        (Complex.continuous_conj.comp (hψ.comp (continuous_subtype_val.comp continuous_fst))))).congr
      (fun p => (he p).symm)
  have hAbs : Integrable (fun a : A => ‖h a‖) dg :=
    hh.norm.integrable_of_hasCompactSupport hhSupp.norm
  have hPI : Integrable P ((ν).prod dg) := by
    apply ((hAbs.const_mul (Cf * D ^ r * Cψ)).comp_snd ν).mono' hPCont.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun p => ?_
    obtain ⟨x, hx⟩ := LeftCosetSpace.mk_surjective Γ p.1
    obtain ⟨q, hq⟩ := hS x
    have he : LeftCosetSpace.mk Γ (rationalNormOne F G q * x) = p.1 := by
      exact (LeftCosetSpace.mk_subgroup_mul Γ ⟨_, ⟨q, rfl⟩⟩ x).trans hx
    change ‖h p.2 * J f ψ p.2 p.1‖ ≤ Cf * D ^ r * Cψ * ‖h p.2‖
    by_cases ha : p.2 ∈ tsupport h
    · rw [← he, normOneCuspidalPairingIntegrand_mk hfInv hψInv, norm_mul, norm_mul,
        Complex.norm_conj, mul_comm (Cf * D ^ r * Cψ)]
      exact mul_le_mul_of_nonneg_left (hProd _ hq _ ha) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport ha]
  have hxInt (x : Q) : J (rightConvolution F G h f) ψ 1 x = ∫ a, P (x, a) ∂dg := by
    change (∫ a, h a * f ((Quotient.out x : S₁).val * 1 * a) ∂dg) *
      starRingEnd ℂ (ψ (Quotient.out x : S₁).val) = _
    simp only [mul_one, P, normOneCuspidalPairingIntegrand, ← mul_assoc, integral_mul_const]
  refine ⟨hPI.integral_prod_left.congr (Filter.Eventually.of_forall fun x => (hxInt x).symm), ?_⟩
  simp_rw [hxInt]
  rw [integral_integral_swap hPI]
  simp only [P, integral_const_mul]

end Langlands.Global.AdelicGroupPoints
