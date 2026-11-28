import Langlands.Global.AdelicLeviPairingIwasawa
import Langlands.Global.AdelicTestFunctionCompactAverage

/-! # Iwasawa unfolding of Levi pairings for right `K`-finite functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter
open scoped CategoryTheory.MonObj NNReal CompactlySupported Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus _root_.Topology

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "AM" => AdelicGroupPoints F (fam.M J)
local notation "A₁" => normOneSubgroup F (fam.M J)
local notation "X₁" => NormOneRationalQuotient F (fam.M J)
local notation "ι" => map F (fam.M J) G (fam.l J ≫ fam.p J)
local notation "ιU" => map F (fam.U J) G (fam.iU J ≫ fam.p J)

omit [IsAffineHom G.X.hom] in
/-- The compact right average of a compactly supported continuous function with a continuous
weight, as a compactly supported continuous function. -/
def compactRightAverageCc (K : Subgroup A) (hK : IsCompact (K : Set A)) (a : K → ℂ)
    (ha : Continuous a) (β : C_c(A, ℂ)) : C_c(A, ℂ) where
  toFun := maximalCompactRightAverage K hK a β
  continuous_toFun := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    unfold maximalCompactRightAverage
    have h : Continuous fun z : A =>
        ∫ k in (univ : Set K), a k * β (z * k) ∂compactHaarProbability F G K hK :=
      continuous_parametric_integral_of_continuous
        ((ha.comp continuous_snd).mul (β.continuous.comp (continuous_fst.mul
          (continuous_subtype_val.comp continuous_snd)))) isCompact_univ
    simpa only [Measure.restrict_univ] using h
  hasCompactSupport' := by
    let S : Set A := (fun p : A × A => p.1 * p.2⁻¹) '' (tsupport β ×ˢ (K : Set A))
    have hS : IsCompact S := (β.hasCompactSupport.prod hK).image (by fun_prop)
    refine HasCompactSupport.intro hS fun z hz => ?_
    unfold maximalCompactRightAverage
    refine (integral_congr_ae (Eventually.of_forall fun k => ?_)).trans (integral_zero _ _)
    change a k * β (z * k) = 0
    have hzk : z * k ∉ tsupport β := fun hzk => hz ⟨(z * k, k), ⟨hzk, k.2⟩, by simp⟩
    rw [image_eq_zero_of_notMem_tsupport hzk, mul_zero]

/-- Averaging radical kernels over `K` with a continuous weight gives the radical kernel of the
compact right average at `k = 1`. -/
theorem integral_mul_radicalKernel (K : Subgroup A) (hK : IsCompact (K : Set A)) (a : K → ℂ)
    (ha : Continuous a) (β : C_c(A, ℂ)) (g : A) (w : AM) :
    ∫ k, a k * fam.radicalKernel J β g k w ∂compactHaarProbability F G K hK =
      fam.radicalKernel J (compactRightAverageCc K hK a ha β) g 1 w := by
  have := locallyOfFiniteType_unipotent F (fam.isRepresentedBy_unipotent J)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨S, hS, hSupp⟩ := fam.exists_compact_radicalKernel_integrand_support J β
    (isCompact_singleton (x := g)) hK (isCompact_singleton (x := w))
  unfold radicalKernel
  simp_rw [← integral_const_mul]
  have hint : Integrable (fun p : K × AdelicGroupPoints F (fam.U J) =>
      a p.1 * β (g⁻¹ * (ιU p.2 * ι w * (p.1 : A))))
      ((compactHaarProbability F G K hK).prod
        (Measure.haar : Measure (AdelicGroupPoints F (fam.U J)))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (ha.comp continuous_fst).mul (β.continuous.comp (continuous_const.mul
        ((((ιU).continuous.comp continuous_snd).mul continuous_const).mul
          (continuous_subtype_val.comp continuous_fst))))
    · refine HasCompactSupport.intro (isCompact_univ.prod hS) fun p hp => ?_
      have hp2 : p.2 ∉ S := fun h => hp ⟨mem_univ _, h⟩
      rw [hSupp g rfl p.1 p.1.2 w rfl p.2 hp2, mul_zero]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  change _ = maximalCompactRightAverage K hK a β (g⁻¹ * (ιU u * ι w * (1 : A)))
  unfold maximalCompactRightAverage
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [mul_one, mul_assoc]

/-- Iwasawa decomposition of a right convolution of a right `K`-finite function: with
`φ(z k) = ∑_j a_j(k) φ(z k_j)`, the compact integral is absorbed into the averaged kernels
`compactRightAverageCc K a_j β`. -/
theorem rightConvolution_eq_iwasawa_finite (K : Subgroup A)
    (hK : IsIwasawaCompact (fam.p J) K) (c : ℝ≥0)
    (hconv : ∀ (β : C_c(A, ℂ)) (φ : A → ℂ), Continuous φ →
      (∀ (u : AdelicGroupPoints F (fam.U J)) (w : A), φ (ιU u * w) = φ w) →
      ∀ x ∈ normOneSubgroup F (fam.M J), ∀ g : A,
        AdelicGroupPoints.rightConvolution F G β φ (ι x * g) =
          (c : ℝ) • ∫ k, ∫ m, ((fam.leviModulus J m : ℝ))⁻¹ •
            (fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k : A)))
            ∂(Measure.haar : Measure AM) ∂(compactHaarProbability F G K hK.isCompact))
    (β : C_c(A, ℂ)) (φ : A → ℂ) (hφ : Continuous φ)
    (hφU : ∀ (u : AdelicGroupPoints F (fam.U J)) (w : A), φ (ιU u * w) = φ w)
    {n : ℕ} (k₀ : Fin n → K) (a : Fin n → K → ℂ) (ha : ∀ j, Continuous (a j))
    (hdec : ∀ (k : K) (z : A), φ (z * k) = ∑ j, a j k * φ (z * k₀ j))
    (x : AM) (hx : x ∈ normOneSubgroup F (fam.M J)) (g : A) :
    AdelicGroupPoints.rightConvolution F G β φ (ι x * g) =
      (c : ℝ) • ∑ j, ∫ m, ((fam.leviModulus J m : ℝ))⁻¹ •
        (fam.radicalKernel J (compactRightAverageCc K hK.isCompact (a j) (ha j) β) g 1
          (x⁻¹ * m) * φ (ι m * (k₀ j : A))) ∂(Measure.haar : Measure AM) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  rw [hconv β φ hφ hφU x hx g]
  congr 1
  obtain ⟨C, hC, hCs⟩ := fam.exists_compact_radicalKernel_support J β
    (isCompact_singleton (x := g)) hK.isCompact
  set C' : Set AM := (fun w => x * w) '' C with hC'def
  have hC' : IsCompact C' := hC.image (continuous_const.mul continuous_id)
  have hδ : Continuous fun z : AM => ((fam.leviModulus J z : ℝ))⁻¹ :=
    (NNReal.continuous_coe.comp (fam.continuous_leviModulus J)).inv₀ fun z =>
      (NNReal.coe_pos.mpr (fam.leviModulus_pos J z)).ne'
  let Fj : Fin n → K → AM → ℂ := fun j k m => ((fam.leviModulus J m : ℝ))⁻¹ •
    (a j k * fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k₀ j : A)))
  have hcont : ∀ j, Continuous fun p : K × AM => Fj j p.1 p.2 := by
    intro j
    have hK' := (fam.continuous_radicalKernel J β).comp
      (continuous_const.prodMk ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_const.mul continuous_snd)) :
        Continuous fun p : K × AM => (g, ((p.1 : A), x⁻¹ * p.2)))
    exact (hδ.comp continuous_snd).smul ((((ha j).comp continuous_fst).mul hK').mul
      (hφ.comp (((ι).continuous.comp continuous_snd).mul continuous_const)))
  have hzero : ∀ (k : K) (m : AM), m ∉ C' → fam.radicalKernel J β g k (x⁻¹ * m) = 0 := by
    intro k m hm
    by_contra hne
    exact hm ⟨x⁻¹ * m, hCs g rfl k k.2 _ hne, by simp⟩
  have hint : ∀ j, Integrable (fun p : K × AM => Fj j p.1 p.2)
      ((compactHaarProbability F G K hK.isCompact).prod (Measure.haar : Measure AM)) := by
    intro j
    refine (hcont j).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_univ.prod hC') fun p hp => ?_
    have hp2 : p.2 ∉ C' := fun h => hp ⟨mem_univ _, h⟩
    change ((fam.leviModulus J p.2 : ℝ))⁻¹ •
      (a j p.1 * fam.radicalKernel J β g p.1 (x⁻¹ * p.2) * φ (ι p.2 * (k₀ j : A))) = 0
    rw [hzero p.1 p.2 hp2, mul_zero, zero_mul, smul_zero]
  have hslice : ∀ j (k : K), Integrable (fun m => Fj j k m) (Measure.haar : Measure AM) := by
    intro j k
    refine ((hcont j).comp (continuous_const.prodMk continuous_id :
      Continuous fun m : AM => (k, m))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hC' fun m hm => ?_
    change ((fam.leviModulus J m : ℝ))⁻¹ •
      (a j k * fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k₀ j : A))) = 0
    rw [hzero k m hm, mul_zero, zero_mul, smul_zero]
  have hpt : ∀ (k : K) (m : AM), ((fam.leviModulus J m : ℝ))⁻¹ •
      (fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k : A))) = ∑ j, Fj j k m := by
    intro k m
    rw [hdec k (ι m), Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = ((fam.leviModulus J m : ℝ))⁻¹ •
      (a j k * fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k₀ j : A)))
    congr 1
    ring
  calc ∫ k, ∫ m, ((fam.leviModulus J m : ℝ))⁻¹ •
        (fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k : A)))
        ∂(Measure.haar : Measure AM) ∂(compactHaarProbability F G K hK.isCompact)
      = ∫ k, ∑ j, ∫ m, Fj j k m ∂(Measure.haar : Measure AM)
          ∂(compactHaarProbability F G K hK.isCompact) := by
        refine integral_congr_ae (Eventually.of_forall fun k => ?_)
        dsimp only
        simp_rw [hpt k]
        exact integral_finsetSum _ fun j _ => hslice j k
    _ = ∑ j, ∫ k, ∫ m, Fj j k m ∂(Measure.haar : Measure AM)
          ∂(compactHaarProbability F G K hK.isCompact) :=
        integral_finsetSum _ fun j _ => (hint j).integral_prod_left
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_integral_swap (hint j)]
        refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        dsimp only [Fj]
        rw [integral_smul, integral_mul_const,
          fam.integral_mul_radicalKernel J K hK.isCompact (a j) (ha j) β g (x⁻¹ * m)]

/-- For a fixed point `k` of the compact group, the Iwasawa integrand is integrable on
`X₁ × M_J(𝔸)` under the domination hypothesis. -/
theorem integrable_iwasawaPairingIntegrand_fixed (K : Subgroup A) (hK : IsCompact (K : Set A))
    (β : C_c(A, ℂ)) (φ : A → ℂ) (hφ : Continuous φ)
    (hφM : ∀ (r : RationalGroupPoints F (fam.M J)) (w : A), φ (ι (rational F (fam.M J) r) * w) = φ w)
    (t : AM → ℂ) (ht : Continuous fun x : A₁ => t x)
    (htM : ∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x)
    (g : A)
    (hdom : ∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
      Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
      ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
        ‖φ (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ * ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ)
    (k : K) :
    Integrable (fun p : X₁ × AM =>
      fam.iwasawaPairingIntegrand J β φ t g k ((Quotient.out p.1 : A₁) : AM) p.2)
      ((normOneRationalQuotientHaarMeasure F (fam.M J)).prod (Measure.haar : Measure AM)) := by
  obtain ⟨C, hC, B, hB0, hbound⟩ := fam.exists_iwasawaPairingIntegrand_bound J K hK β φ t g
  obtain ⟨W, hW, hWae⟩ := hdom C hC
  have hind : Integrable (C.indicator fun _ => B) (Measure.haar : Measure AM) :=
    (integrableOn_const hC.measure_lt_top.ne).integrable_indicator hC.measurableSet
  have hcont := (fam.continuous_iwasawaPairingIntegrand J K β φ hφ hφM t ht htM g).comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd) :
      Continuous fun p : X₁ × AM => (p.1, (k, p.2)))
  refine Integrable.mono' (hW.mul_prod hind) hcont.aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae hWae] with p hp
  refine (hbound _ _ _).trans ?_
  by_cases hz : p.2 ∈ C
  · rw [indicator_of_mem hz, mul_comm]
    exact mul_le_mul_of_nonneg_right (hp k p.2 hz) hB0
  · rw [indicator_of_notMem hz, zero_mul, mul_zero]

section Decomposition

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

local notation "pp" => positivePointMap F (fam.M J) T i
local notation "νP" => normalizedPositiveHaarMeasure F (fam.M J) T i hi I e hc

include hi I e hc in
/-- For a fixed point `k` of the compact group, the Iwasawa double integral over
`X₁ × M_J(𝔸)` in positive and norm-one coordinates. -/
theorem integral_iwasawaPairingIntegrand_fixed_eq (K : Subgroup A)
    (hK : IsCompact (K : Set A))
    (β : C_c(A, ℂ)) (φ : A → ℂ) (hφ : Continuous φ)
    (hφM : ∀ (r : RationalGroupPoints F (fam.M J)) (w : A), φ (ι (rational F (fam.M J) r) * w) = φ w)
    (t : AM → ℂ) (ht : Continuous fun x : A₁ => t x)
    (htM : ∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x)
    (g : A)
    (hdom : ∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
      Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
      ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
        ‖φ (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ * ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ)
    (k : K) :
    ∫ ξ, ∫ z, fam.iwasawaPairingIntegrand J β φ t g k ((Quotient.out ξ : A₁) : AM) z
        ∂(Measure.haar : Measure AM) ∂normOneRationalQuotientHaarMeasure F (fam.M J) =
      ∫ b, ((fam.leviModulus J (pp b) : ℝ))⁻¹ •
        ∫ ξ, φ (ι (pp b * ((Quotient.out ξ : A₁) : AM)) * k) *
          ∫ x : A₁, fam.radicalKernel J β g k
            (pp b * ((x : AM)⁻¹ * ((Quotient.out ξ : A₁) : AM))) * starRingEnd ℂ (t x)
          ∂Measure.haar ∂normOneRationalQuotientHaarMeasure F (fam.M J) ∂νP := by
  have hInt := fam.integrable_iwasawaPairingIntegrand_fixed J K hK β φ hφ hφM t ht htM g hdom k
  rw [integral_integral_swap hInt]
  refine (fam.integral_eq_integral_positive_normOne J T i hi I e hc _
    hInt.integral_prod_right).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  dsimp only
  rw [← integral_integral_swap (fam.integrable_iwasawaPairingIntegrand_normOne J T i hi I e K hK
    β φ hφ hφM t ht htM g hdom k b)]
  exact fam.integral_iwasawaPairingIntegrand_normOne_eq J T i hi I e hc K hK β φ hφ hφM t ht htM
    g hdom k b

include hi I e hc in
/-- **Iwasawa unfolding of the norm-one Levi pairing of a right convolution of a right
`K`-finite function.** If `φ(z k) = ∑_j a_j(k) φ(z k_j)` with continuous `a_j`, then
`leviPairing J (β * φ) g t = c ∑_j ∫_{A⁺} δ(b)⁻¹ ∫_{X₁} φ(ι(b y) k_j)
  ∫_{M_J(𝔸)¹} K_j(b x⁻¹ y) conj t(x) dx dy db`, where `K_j` is the radical kernel at `(g, 1)` of the
compact right average of `β` with weight `a_j`. -/
theorem leviPairing_rightConvolution_eq_iwasawa_finite (K : Subgroup A)
    (hK : IsIwasawaCompact (fam.p J) K) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (β : C_c(A, ℂ)) (φ : A → ℂ), Continuous φ →
      (∀ (u : AdelicGroupPoints F (fam.U J)) (w : A), φ (ιU u * w) = φ w) →
      (∀ (r : RationalGroupPoints F (fam.M J)) (w : A),
        φ (ι (rational F (fam.M J) r) * w) = φ w) →
      ∀ {n : ℕ} (k₀ : Fin n → K) (a : Fin n → K → ℂ) (ha : ∀ j, Continuous (a j)),
      (∀ (k : K) (z : A), φ (z * k) = ∑ j, a j k * φ (z * k₀ j)) →
      ∀ (t : AM → ℂ), (Continuous fun x : A₁ => t x) →
      (∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x) →
      ∀ g : A, (∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
        Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
        ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
          ‖φ (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ *
            ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ) →
        fam.leviPairing J (AdelicGroupPoints.rightConvolution F G β φ) g t =
          (c : ℝ) • ∑ j, ∫ b, ((fam.leviModulus J (pp b) : ℝ))⁻¹ •
            ∫ ξ, φ (ι (pp b * ((Quotient.out ξ : A₁) : AM)) * (k₀ j : A)) *
              ∫ x : A₁, fam.radicalKernel J (compactRightAverageCc K hK.isCompact (a j) (ha j) β)
                g 1 (pp b * ((x : AM)⁻¹ * ((Quotient.out ξ : A₁) : AM))) * starRingEnd ℂ (t x)
              ∂Measure.haar ∂normOneRationalQuotientHaarMeasure F (fam.M J) ∂νP := by
  obtain ⟨c, hc0, hconv⟩ := fam.exists_rightConvolution_eq_iwasawa J K hK
  refine ⟨c, hc0, fun β φ hφ hφU hφM n k₀ a ha hdec t ht htM g hdom => ?_⟩
  have hK' := hK.isCompact
  let βj : Fin n → C_c(A, ℂ) := fun j => compactRightAverageCc K hK' (a j) (ha j) β
  let φj : Fin n → A → ℂ := fun j w => φ (w * (k₀ j : A))
  have hφjc : ∀ j, Continuous (φj j) := fun j => hφ.comp (continuous_id.mul continuous_const)
  have hφjM : ∀ j (r : RationalGroupPoints F (fam.M J)) (w : A),
      φj j (ι (rational F (fam.M J) r) * w) = φj j w := fun j r w => by
    change φ (ι (rational F (fam.M J) r) * w * _) = φ (w * _)
    rw [mul_assoc, hφM]
  have hdomj : ∀ j, ∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
      Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
      ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
        ‖φj j (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ *
          ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ := by
    intro j C hC
    obtain ⟨W, hW, hWae⟩ := hdom C hC
    refine ⟨W, hW, ?_⟩
    filter_upwards [hWae] with ξ hξ
    intro k z hz
    have := hξ (k * k₀ j) z hz
    change ‖φ (ι _ * (k : A) * (k₀ j : A))‖ * _ ≤ _
    rw [mul_assoc]
    exact this
  have hone : ((1 : K) : A) = 1 := rfl
  have hstep1 : ∀ ξ : X₁, fam.leviPairingIntegrand J
      (AdelicGroupPoints.rightConvolution F G β φ) g t ξ =
      (c : ℝ) • ∑ j, ∫ z, fam.iwasawaPairingIntegrand J (βj j) (φj j) t g (1 : K)
        ((Quotient.out ξ : A₁) : AM) z ∂(Measure.haar : Measure AM) := by
    intro ξ
    set x : A₁ := Quotient.out ξ with hxdef
    change AdelicGroupPoints.rightConvolution F G β φ (ι (x : AM) * g) *
      starRingEnd ℂ (t x) = _
    rw [fam.rightConvolution_eq_iwasawa_finite J K hK c hconv β φ hφ hφU k₀ a ha hdec
      (x : AM) x.property g, smul_mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_mul_const]
    refine (integral_mul_left_eq_self _ (x : AM)).symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [iwasawaPairingIntegrand, inv_mul_cancel_left,
      fam.leviModulus_mul_normOne J x.property, hone, mul_one]
    rfl
  unfold leviPairing
  rw [integral_congr_ae (Eventually.of_forall hstep1), integral_smul,
    integral_finsetSum _ fun j _ => (fam.integrable_iwasawaPairingIntegrand_fixed J K hK'
      (βj j) (φj j) (hφjc j) (hφjM j) t ht htM g (hdomj j) 1).integral_prod_left]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fam.integral_iwasawaPairingIntegrand_fixed_eq J T i hi I e hc K hK' (βj j) (φj j)
    (hφjc j) (hφjM j) t ht htM g (hdomj j) 1]
  simp only [φj, hone, mul_one]
  rfl

end Decomposition

end StandardParabolicFamily

end Langlands.Global
