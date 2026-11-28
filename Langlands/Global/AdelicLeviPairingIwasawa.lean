import Langlands.Global.AdelicStandardParabolicIwasawa
import Langlands.Global.LeftCosetDiagonalSwap
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.AdelicGroupPolish

/-! # Iwasawa unfolding of the norm-one Levi pairing of a right convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter
open scoped CategoryTheory.MonObj NNReal CompactlySupported

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus _root_.Topology

section TripleIntegral

variable {α β Z E : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Z]
  {m₁ : Measure α} {m₂ : Measure β} {m₃ : Measure Z} [SFinite m₁] [SFinite m₂] [SFinite m₃]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Moving the outer variable of an integrable triple integral innermost. -/
theorem integral_integral_integral_comm (f : α → β → Z → E)
    (hf : Integrable (fun p : α × (β × Z) => f p.1 p.2.1 p.2.2) (m₁.prod (m₂.prod m₃))) :
    ∫ a, ∫ b, ∫ c, f a b c ∂m₃ ∂m₂ ∂m₁ = ∫ b, ∫ c, ∫ a, f a b c ∂m₁ ∂m₃ ∂m₂ := by
  calc ∫ a, ∫ b, ∫ c, f a b c ∂m₃ ∂m₂ ∂m₁ = ∫ a, ∫ q, f a q.1 q.2 ∂(m₂.prod m₃) ∂m₁ := by
        refine integral_congr_ae ?_
        filter_upwards [hf.prod_right_ae] with a ha
        exact (integral_prod _ ha).symm
    _ = ∫ q, ∫ a, f a q.1 q.2 ∂m₁ ∂(m₂.prod m₃) :=
        integral_integral_swap (f := fun a (q : β × Z) => f a q.1 q.2) hf
    _ = _ := integral_prod _ hf.integral_prod_right

end TripleIntegral

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

/-- The Iwasawa integrand of a norm-one Levi pairing: `δ(z)⁻¹ K(z) φ(ι(x z) k) conj t(x)`. -/
def iwasawaPairingIntegrand (β : A → ℂ) (φ : A → ℂ) (t : AM → ℂ) (g k : A) (x z : AM) : ℂ :=
  ((fam.leviModulus J z : ℝ))⁻¹ • (fam.radicalKernel J β g k z * φ (ι (x * z) * k)) *
    starRingEnd ℂ (t x)

/-- For continuous `φ` and `t` (on norm-one points), both left invariant under rational Levi
points, the Iwasawa integrand read at representatives is continuous on `X₁ × (K × M_J(𝔸))`. -/
theorem continuous_iwasawaPairingIntegrand (K : Subgroup A) (β : C_c(A, ℂ)) (φ : A → ℂ)
    (hφ : Continuous φ)
    (hφM : ∀ (r : RationalGroupPoints F (fam.M J)) (w : A), φ (ι (rational F (fam.M J) r) * w) = φ w)
    (t : AM → ℂ) (ht : Continuous fun x : A₁ => t x)
    (htM : ∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x)
    (g : A) :
    Continuous fun p : X₁ × (K × AM) =>
      fam.iwasawaPairingIntegrand J β φ t g p.2.1 ((Quotient.out p.1 : A₁) : AM) p.2.2 := by
  have hδ : Continuous fun z : AM => ((fam.leviModulus J z : ℝ))⁻¹ :=
    (NNReal.continuous_coe.comp (fam.continuous_leviModulus J)).inv₀ fun z =>
      (NNReal.coe_pos.mpr (fam.leviModulus_pos J z)).ne'
  have hK := fam.continuous_radicalKernel J β
  refine LeftCosetSpace.continuous_out_prod' (rationalNormOneSubgroup F (fam.M J))
    (fun p : A₁ × (K × AM) => fam.iwasawaPairingIntegrand J β φ t g p.2.1 (p.1 : AM) p.2.2)
    ?_ ?_
  · unfold iwasawaPairingIntegrand
    refine ((hδ.comp (continuous_snd.comp continuous_snd)).smul ?_).mul
      ((ht.comp continuous_fst).star)
    refine (hK.comp (continuous_const.prodMk ((continuous_subtype_val.comp
      (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)))).mul ?_
    exact hφ.comp ((((ι).continuous.comp ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_snd.comp continuous_snd))).mul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))
  · rintro ⟨_, r, rfl⟩ x ⟨k, z⟩
    unfold iwasawaPairingIntegrand
    have h1 : ((rationalNormOne F (fam.M J) r : A₁) : AM) = rational F (fam.M J) r := rfl
    simp only [Subgroup.coe_mul, h1, mul_assoc, map_mul, htM]
    rw [hφM]

/-- On the radical kernel's support the Iwasawa integrand is bounded by a multiple of
`‖φ(ι(x z) k)‖ ‖t(x)‖`, uniformly for `k ∈ K`. -/
theorem exists_iwasawaPairingIntegrand_bound (K : Subgroup A) (hK : IsCompact (K : Set A))
    (β : C_c(A, ℂ)) (φ : A → ℂ) (t : AM → ℂ) (g : A) :
    ∃ C : Set AM, IsCompact C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ (k : K) (x z : AM),
      ‖fam.iwasawaPairingIntegrand J β φ t g k x z‖ ≤
        C.indicator (fun _ => B) z * (‖φ (ι (x * z) * k)‖ * ‖t x‖) := by
  obtain ⟨C, hC, hsupp⟩ := fam.exists_compact_radicalKernel_support J β
    (isCompact_singleton (x := g)) hK
  have hcont : Continuous fun q : A × AM =>
      ((fam.leviModulus J q.2 : ℝ))⁻¹ * ‖fam.radicalKernel J β g q.1 q.2‖ := by
    have hδ : Continuous fun z : AM => ((fam.leviModulus J z : ℝ))⁻¹ :=
      (NNReal.continuous_coe.comp (fam.continuous_leviModulus J)).inv₀ fun z =>
        (NNReal.coe_pos.mpr (fam.leviModulus_pos J z)).ne'
    exact (hδ.comp continuous_snd).mul ((fam.continuous_radicalKernel J β).comp
      (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))).norm
  obtain ⟨B, hB⟩ := (hK.prod hC).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, hC, max B 0, le_max_right _ _, fun k x z => ?_⟩
  by_cases hz : z ∈ C
  · rw [indicator_of_mem hz]
    have hle := hB (k.val, z) ⟨k.property, hz⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg _))
      (norm_nonneg _))] at hle
    unfold iwasawaPairingIntegrand
    rw [norm_mul, norm_smul, norm_mul, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg _))]
    calc ((fam.leviModulus J z : ℝ))⁻¹ * (‖fam.radicalKernel J β g k z‖ *
          ‖φ (ι (x * z) * k)‖) * ‖t x‖
        = (((fam.leviModulus J z : ℝ))⁻¹ * ‖fam.radicalKernel J β g k z‖) *
          (‖φ (ι (x * z) * k)‖ * ‖t x‖) := by ring
      _ ≤ max B 0 * (‖φ (ι (x * z) * k)‖ * ‖t x‖) :=
        mul_le_mul_of_nonneg_right (hle.trans (le_max_left _ _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · rw [indicator_of_notMem hz, zero_mul]
    have h0 : fam.radicalKernel J β g k z = 0 := by
      by_contra hne
      exact hz (hsupp g rfl k k.property z hne)
    unfold iwasawaPairingIntegrand
    rw [h0, zero_mul, smul_zero, zero_mul, norm_zero]

/-- Under a domination hypothesis on the fibres of `φ` and on `t`, the Iwasawa integrand of
the pairing is integrable on `X₁ × (K × M(𝔸))`. -/
theorem integrable_iwasawaPairingIntegrand (K : Subgroup A) (hK : IsCompact (K : Set A))
    (β : C_c(A, ℂ)) (φ : A → ℂ) (hφ : Continuous φ)
    (hφM : ∀ (r : RationalGroupPoints F (fam.M J)) (w : A), φ (ι (rational F (fam.M J) r) * w) = φ w)
    (t : AM → ℂ) (ht : Continuous fun x : A₁ => t x)
    (htM : ∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x)
    (g : A)
    (hdom : ∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
      Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
      ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
        ‖φ (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ * ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ) :
    Integrable (fun p : X₁ × (K × AM) =>
      fam.iwasawaPairingIntegrand J β φ t g p.2.1 ((Quotient.out p.1 : A₁) : AM) p.2.2)
      ((normOneRationalQuotientHaarMeasure F (fam.M J)).prod
        ((compactHaarProbability F G K hK).prod (Measure.haar : Measure AM))) := by
  obtain ⟨C, hC, B, hB0, hbound⟩ := fam.exists_iwasawaPairingIntegrand_bound J K hK β φ t g
  obtain ⟨W, hW, hWae⟩ := hdom C hC
  have hind : Integrable (fun q : K × AM => C.indicator (fun _ => B) q.2)
      ((compactHaarProbability F G K hK).prod (Measure.haar : Measure AM)) := by
    have h1 : Integrable (C.indicator fun _ => B) (Measure.haar : Measure AM) :=
      (integrableOn_const hC.measure_lt_top.ne).integrable_indicator hC.measurableSet
    have h2 := (integrable_const (1 : ℝ) :
      Integrable (fun _ : K => (1 : ℝ)) (compactHaarProbability F G K hK)).mul_prod h1
    simpa only [one_mul] using h2
  refine Integrable.mono' (hW.mul_prod hind)
    (fam.continuous_iwasawaPairingIntegrand J K β φ hφ hφM t ht htM g).aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae hWae] with p hp
  refine (hbound _ _ _).trans ?_
  by_cases hz : p.2.2 ∈ C
  · rw [indicator_of_mem hz, mul_comm]
    exact mul_le_mul_of_nonneg_right (hp p.2.1 p.2.2 hz) hB0
  · rw [indicator_of_notMem hz, zero_mul, mul_zero]

/-- First unfolding: the pairing of a right convolution is the Iwasawa integral of
`iwasawaPairingIntegrand`, the Levi variable being translated by the norm-one point. -/
theorem leviPairing_eq_integral_iwasawaPairingIntegrand (K : Subgroup A)
    (hK : IsIwasawaCompact (fam.p J) K) (c : ℝ≥0) (β : C_c(A, ℂ)) (φ : A → ℂ)
    (t : AM → ℂ) (g : A)
    (hconv : ∀ x ∈ normOneSubgroup F (fam.M J),
      AdelicGroupPoints.rightConvolution F G β φ (ι x * g) =
        (c : ℝ) • ∫ k, ∫ m, ((fam.leviModulus J m : ℝ))⁻¹ •
          (fam.radicalKernel J β g k (x⁻¹ * m) * φ (ι m * (k : A)))
          ∂(Measure.haar : Measure AM) ∂(compactHaarProbability F G K hK.isCompact)) :
    fam.leviPairing J (AdelicGroupPoints.rightConvolution F G β φ) g t =
      (c : ℝ) • ∫ ξ, ∫ k, ∫ z, fam.iwasawaPairingIntegrand J β φ t g k
        ((Quotient.out ξ : A₁) : AM) z ∂(Measure.haar : Measure AM)
        ∂(compactHaarProbability F G K hK.isCompact)
        ∂normOneRationalQuotientHaarMeasure F (fam.M J) := by
  unfold leviPairing
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  set x : A₁ := Quotient.out ξ with hxdef
  change AdelicGroupPoints.rightConvolution F G β φ (ι (x : AM) * g) *
    starRingEnd ℂ (t x) = _
  rw [hconv x x.property, smul_mul_assoc, ← integral_mul_const]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  dsimp only
  rw [← integral_mul_const]
  refine (integral_mul_left_eq_self _ (x : AM)).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [iwasawaPairingIntegrand, inv_mul_cancel_left,
    fam.leviModulus_mul_normOne J x.property]
  rfl

section Decomposition

variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ fam.M J)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

local notation "pp" => positivePointMap F (fam.M J) T i
local notation "νP" => normalizedPositiveHaarMeasure F (fam.M J) T i hi I e hc

/-- Integration over `M_J(𝔸)` in positive and norm-one coordinates. -/
theorem integral_eq_integral_positive_normOne (f : AM → ℂ)
    (hf : Integrable f (Measure.haar : Measure AM)) :
    ∫ z, f z ∂(Measure.haar : Measure AM) =
      ∫ b, ∫ n : A₁, f (pp b * (n : AM)) ∂Measure.haar ∂νP := by
  have := positiveSecondCountableTopology F T I e
  have := normalizedPositiveHaarMeasure_sigmaFinite F (fam.M J) T i hi I e hc
  have hmp := measurePreserving_normOneDecomposition F (fam.M J) T i hi I e hc
  have hemb := (normOneDecomposition F (fam.M J) T i hi I e).measurableEmbedding
  rw [← hmp.integral_comp hemb]
  exact integral_prod _ ((hmp.integrable_comp_emb hemb).mpr hf)

include hi I e in
/-- For fixed `k` and positive `b`, the Iwasawa integrand on `X₁ × M_J(𝔸)¹` at the Levi point
`b n` is integrable. -/
theorem integrable_iwasawaPairingIntegrand_normOne (K : Subgroup A) (hK : IsCompact (K : Set A))
    (β : C_c(A, ℂ)) (φ : A → ℂ) (hφ : Continuous φ)
    (hφM : ∀ (r : RationalGroupPoints F (fam.M J)) (w : A), φ (ι (rational F (fam.M J) r) * w) = φ w)
    (t : AM → ℂ) (ht : Continuous fun x : A₁ => t x)
    (htM : ∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x)
    (g : A)
    (hdom : ∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
      Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
      ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
        ‖φ (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ * ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ)
    (k : K) (b : intrinsicSubgroup F T) :
    Integrable (fun p : X₁ × A₁ =>
      fam.iwasawaPairingIntegrand J β φ t g k ((Quotient.out p.1 : A₁) : AM) (pp b * (p.2 : AM)))
      ((normOneRationalQuotientHaarMeasure F (fam.M J)).prod (Measure.haar : Measure A₁)) := by
  obtain ⟨C, hC, B, hB0, hbound⟩ := fam.exists_iwasawaPairingIntegrand_bound J K hK β φ t g
  obtain ⟨W, hW, hWae⟩ := hdom C hC
  set C' : Set A₁ := normOneFactor F (fam.M J) T i hi I e '' C with hC'def
  have hC' : IsCompact C' := hC.image (continuous_normOneFactor F (fam.M J) T i hi I e)
  have hmem : ∀ n : A₁, pp b * (n : AM) ∈ C → n ∈ C' := by
    intro n hn
    refine ⟨_, hn, Subtype.ext ?_⟩
    rw [normOneFactor_val, positiveFactor_mul_normOne, inv_mul_cancel_left]
  have hind : Integrable (C'.indicator fun _ => B) (Measure.haar : Measure A₁) :=
    (integrableOn_const hC'.measure_lt_top.ne).integrable_indicator hC'.measurableSet
  have hcont := (fam.continuous_iwasawaPairingIntegrand J K β φ hφ hφM t ht htM g).comp
    (continuous_fst.prodMk (continuous_const.prodMk
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd))) :
      Continuous fun p : X₁ × A₁ => (p.1, (k, pp b * (p.2 : AM))))
  refine Integrable.mono' (hW.norm.mul_prod hind) hcont.aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae hWae] with p hp
  refine (hbound _ _ _).trans ?_
  by_cases hz : pp b * (p.2 : AM) ∈ C
  · rw [indicator_of_mem hz, indicator_of_mem (hmem _ hz), mul_comm]
    exact mul_le_mul_of_nonneg_right ((hp k _ hz).trans (Real.le_norm_self _)) hB0
  · rw [indicator_of_notMem hz, zero_mul]
    exact mul_nonneg (norm_nonneg _) (indicator_nonneg (fun _ _ => hB0) _)

include hi I e hc in
/-- For fixed `k` and positive `b`, the diagonal exchange on `X₁ × M_J(𝔸)¹` turns the Iwasawa
integral into the pairing of the fibre of `φ` at `b k` with the convolution of `t` against the
radical kernel. -/
theorem integral_iwasawaPairingIntegrand_normOne_eq (K : Subgroup A) (hK : IsCompact (K : Set A))
    (β : C_c(A, ℂ)) (φ : A → ℂ) (hφ : Continuous φ)
    (hφM : ∀ (r : RationalGroupPoints F (fam.M J)) (w : A), φ (ι (rational F (fam.M J) r) * w) = φ w)
    (t : AM → ℂ) (ht : Continuous fun x : A₁ => t x)
    (htM : ∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x)
    (g : A)
    (hdom : ∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
      Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
      ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
        ‖φ (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ * ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ)
    (k : K) (b : intrinsicSubgroup F T) :
    ∫ ξ, ∫ n : A₁, fam.iwasawaPairingIntegrand J β φ t g k ((Quotient.out ξ : A₁) : AM)
        (pp b * (n : AM)) ∂Measure.haar ∂normOneRationalQuotientHaarMeasure F (fam.M J) =
      ((fam.leviModulus J (pp b) : ℝ))⁻¹ • ∫ ξ, φ (ι (pp b * ((Quotient.out ξ : A₁) : AM)) * k) *
        ∫ x : A₁, fam.radicalKernel J β g k (pp b * ((x : AM)⁻¹ * ((Quotient.out ξ : A₁) : AM))) *
          starRingEnd ℂ (t x) ∂Measure.haar ∂normOneRationalQuotientHaarMeasure F (fam.M J) := by
  have hM : IsConnectedReductive (fam.M J) := (fam.isCompatible J).levi.isConnectedReductive
  have := normOneHaarRightInvariant F (fam.M J) hM.smooth hM.connectedSpace
  set δ : ℝ := (fam.leviModulus J (pp b) : ℝ) with hδdef
  have hδpos : 0 < δ := NNReal.coe_pos.mpr (fam.leviModulus_pos J _)
  let Φ : A₁ → A₁ → ℂ := fun x y =>
    fam.radicalKernel J β g k (pp b * ((x : AM)⁻¹ * (y : AM))) * φ (ι (pp b * (y : AM)) * k) *
      starRingEnd ℂ (t x)
  have hcomm : ∀ x y : AM, x * (pp b * y) = pp b * (x * y) := fun x y => by
    rw [← mul_assoc, ← mul_assoc, (positivePointMap_commute F (fam.M J) T i hc b x).eq]
  have hpt : ∀ x n : A₁, fam.iwasawaPairingIntegrand J β φ t g k (x : AM) (pp b * (n : AM)) =
      δ⁻¹ • Φ x (x * n) := by
    intro x n
    simp only [iwasawaPairingIntegrand, Φ, Subgroup.coe_mul, inv_mul_cancel_left, hcomm,
      fam.leviModulus_mul, fam.leviModulus_eq_one_of_mem_normOne J n.property, mul_one,
      smul_mul_assoc, hδdef]
  have hΦc : Continuous fun p : A₁ × A₁ => Φ p.1 p.2 := by
    refine (((fam.continuous_radicalKernel J β).comp (continuous_const.prodMk
      (continuous_const.prodMk (continuous_const.mul
        ((continuous_subtype_val.comp continuous_fst).inv.mul
          (continuous_subtype_val.comp continuous_snd)))))).mul
      (hφ.comp (((ι).continuous.comp (continuous_const.mul
        (continuous_subtype_val.comp continuous_snd))).mul continuous_const))).mul
      (ht.comp continuous_fst).star
  have hinv : ∀ (w : rationalNormOneSubgroup F (fam.M J)) (x y : A₁),
      Φ ((w : A₁) * x) ((w : A₁) * y) = Φ x y := by
    rintro ⟨_, r, rfl⟩ x y
    have h1 : ((rationalNormOne F (fam.M J) r : A₁) : AM) = rational F (fam.M J) r := rfl
    have e1 : ((rational F (fam.M J) r * (x : AM)))⁻¹ * (rational F (fam.M J) r * (y : AM)) =
        (x : AM)⁻¹ * (y : AM) := by group
    have e2 : φ (ι (pp b * (rational F (fam.M J) r * (y : AM))) * k) =
        φ (ι (pp b * (y : AM)) * k) := by
      rw [← hcomm, map_mul, mul_assoc, hφM]
    simp only [Φ, Subgroup.coe_mul, h1, e1, e2, htM]
  have hint : Integrable (fun p : NormOneRationalQuotient F (fam.M J) × A₁ =>
      Φ (Quotient.out p.1) (Quotient.out p.1 * p.2))
      ((normOneRationalQuotientHaarMeasure F (fam.M J)).prod (Measure.haar : Measure A₁)) := by
    have h := (fam.integrable_iwasawaPairingIntegrand_normOne J T i hi I e K hK β φ hφ hφM t ht
      htM g hdom k b).smul δ
    refine h.congr (Eventually.of_forall fun p => ?_)
    change δ • fam.iwasawaPairingIntegrand J β φ t g k ((Quotient.out p.1 : A₁) : AM)
      (pp b * (p.2 : AM)) = _
    rw [hpt, smul_inv_smul₀ hδpos.ne']
  have hswap := LeftCosetSpace.integral_integral_swap_diagonal (rationalNormOneSubgroup F (fam.M J))
    (isDiscrete_rationalNormOneSubgroup F (fam.M J)) Φ hΦc hinv hint
  calc ∫ ξ, ∫ n : A₁, fam.iwasawaPairingIntegrand J β φ t g k ((Quotient.out ξ : A₁) : AM)
        (pp b * (n : AM)) ∂Measure.haar ∂normOneRationalQuotientHaarMeasure F (fam.M J)
      = ∫ ξ, δ⁻¹ • ∫ y : A₁, Φ (Quotient.out ξ) y ∂Measure.haar
          ∂normOneRationalQuotientHaarMeasure F (fam.M J) := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [← integral_smul]
        refine (integral_congr_ae (Eventually.of_forall fun n => hpt _ n)).trans ?_
        exact integral_mul_left_eq_self (fun y => δ⁻¹ • Φ (Quotient.out ξ) y) (Quotient.out ξ)
    _ = δ⁻¹ • ∫ ξ, ∫ x : A₁, Φ x (Quotient.out ξ) ∂Measure.haar
          ∂normOneRationalQuotientHaarMeasure F (fam.M J) := by
        rw [integral_smul]
        congr 1
    _ = _ := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only [Φ]
        ring

/-- **Iwasawa unfolding of the norm-one Levi pairing of a right convolution.** For a compactly
supported continuous `β` on `G(𝔸)`, a continuous `φ` left invariant under `U_J(𝔸) M_J(F)`, a
function `t` on `M_J(𝔸)` continuous on norm-one points and left invariant under `M_J(F)`, and a
point `g`, under a domination hypothesis on the fibres of `φ` and on `t`, the pairing
`∫_{X₁} (β * φ)(ι(x) g) conj t(x) dx` equals
`c ∫_K ∫_{A⁺} δ(b)⁻¹ ∫_{X₁} φ(ι(b y) k) ∫_{M_J(𝔸)¹} K_{g,k}(b x⁻¹ y) conj t(x) dx dy db dk`,
with `K_{g,k}` the radical kernel of `β`. -/
theorem leviPairing_rightConvolution_eq_iwasawa (K : Subgroup A)
    (hK : IsIwasawaCompact (fam.p J) K) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (β : C_c(A, ℂ)) (φ : A → ℂ), Continuous φ →
      (∀ (u : AdelicGroupPoints F (fam.U J)) (w : A), φ (ιU u * w) = φ w) →
      (∀ (r : RationalGroupPoints F (fam.M J)) (w : A),
        φ (ι (rational F (fam.M J) r) * w) = φ w) →
      ∀ (t : AM → ℂ), (Continuous fun x : A₁ => t x) →
      (∀ (r : RationalGroupPoints F (fam.M J)) (x : AM), t (rational F (fam.M J) r * x) = t x) →
      ∀ g : A, (∀ C : Set AM, IsCompact C → ∃ W : X₁ → ℝ,
        Integrable W (normOneRationalQuotientHaarMeasure F (fam.M J)) ∧
        ∀ᵐ ξ ∂normOneRationalQuotientHaarMeasure F (fam.M J), ∀ (k : K) (z : AM), z ∈ C →
          ‖φ (ι (((Quotient.out ξ : A₁) : AM) * z) * k)‖ *
            ‖t ((Quotient.out ξ : A₁) : AM)‖ ≤ W ξ) →
        fam.leviPairing J (AdelicGroupPoints.rightConvolution F G β φ) g t =
          (c : ℝ) • ∫ k, ∫ b, ((fam.leviModulus J (pp b) : ℝ))⁻¹ •
            ∫ ξ, φ (ι (pp b * ((Quotient.out ξ : A₁) : AM)) * k) *
              ∫ x : A₁, fam.radicalKernel J β g k
                (pp b * ((x : AM)⁻¹ * ((Quotient.out ξ : A₁) : AM))) * starRingEnd ℂ (t x)
              ∂Measure.haar ∂normOneRationalQuotientHaarMeasure F (fam.M J) ∂νP
            ∂(compactHaarProbability F G K hK.isCompact) := by
  obtain ⟨c, hc0, hconv⟩ := fam.exists_rightConvolution_eq_iwasawa J K hK
  refine ⟨c, hc0, fun β φ hφ hφU hφM t ht htM g hdom => ?_⟩
  have hK' := hK.isCompact
  rw [fam.leviPairing_eq_integral_iwasawaPairingIntegrand J K hK c β φ t g
    (fun x hx => hconv β φ hφ hφU x hx g)]
  congr 1
  have hInt := fam.integrable_iwasawaPairingIntegrand J K hK' β φ hφ hφM t ht htM g hdom
  rw [integral_integral_integral_comm _ hInt]
  refine integral_congr_ae ?_
  filter_upwards [hInt.integral_prod_right.prod_right_ae] with k hk
  refine (fam.integral_eq_integral_positive_normOne J T i hi I e hc _ hk).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  dsimp only
  rw [← integral_integral_swap (fam.integrable_iwasawaPairingIntegrand_normOne J T i hi I e K hK'
    β φ hφ hφM t ht htM g hdom k b)]
  exact fam.integral_iwasawaPairingIntegrand_normOne_eq J T i hi I e hc K hK' β φ hφ hφM t ht htM
    g hdom k b

end Decomposition

end StandardParabolicFamily

end Langlands.Global
