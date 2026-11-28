import Langlands.Global.AdelicNormOneKernelVector
import Langlands.Analysis.Local.QuotientL2UnfoldingProof

/-! # Kernel vectors paired with continuous square-integrable functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Set
open scoped CategoryTheory.MonObj CompactlySupported

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ H)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

local notation "A" => AdelicGroupPoints F H
local notation "A₁" => normOneSubgroup F H
local notation "Q" => PositiveRationalQuotient F H T i
local notation "q" => LeftCosetSpace.mk (positiveRationalSubgroup F H T i)
local notation "Γ" => positiveRationalSubgroup F H T i
local notation "dq" => positiveRationalQuotientHaarMeasure F H T i
local notation "dg" => (Measure.haar : Measure A)
local notation "dΓ" => positiveRationalSubgroupHaarMeasure F H T i hi I e hc
local notation "V" => Lp ℂ 2 dq
local notation "Pos" => intrinsicSubgroup F T
local notation "νP" => normalizedPositiveHaarMeasure F H T i hi I e hc

local notation "πP" => positiveFactor F H T i hi I e
local notation "π₁" => normOneFactor F H T i hi I e
local notation "ι₀" => positivePointMap F H T i

variable [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant]

include hi e hc in
/-- For a compactly supported continuous `g` on `H(𝔸)` and a continuous square-integrable `f` on
`Q`, the integral of `g · (f ∘ q)` does not change when `f` is replaced by the representative of
its `L²` class. -/
theorem integral_mul_coeFn_toLp (g : C_c(A, ℂ)) (f : Q → ℂ) (hfc : Continuous f)
    (hf2 : MemLp f 2 dq) :
    ∫ a, g a * (hf2.toLp f : Q → ℂ) (q a) ∂dg = ∫ a, g a * f (q a) ∂dg := by
  let := positiveRationalQuotient_borelSpace F H T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F H T i hi I e hc
  have hcompat := positiveRationalQuotientHaarMeasure_isCompatible F H T i hi I e hc
  let f₀ : C_c(A, ℂ) := ⟨⟨fun a => starRingEnd ℂ (g a), continuous_star.comp g.continuous⟩,
    g.hasCompactSupport.comp_left (map_zero _)⟩
  obtain ⟨-, -, v, ℓ, hv, hunf⟩ := Langlands.QuotientIntegration.quotientL2Unfolding Γ
    (isClosed_positiveRationalSubgroup F H T i hi I e hc) dΓ dg dq hcompat f₀
  have h1 := (hunf (hf2.toLp f)).2.2
  have hstar : ∀ a, star (f₀ a) = g a := fun a => by
    change star (starRingEnd ℂ (g a)) = g a
    rw [Complex.star_def, Complex.conj_conj]
  simp only [hstar] at h1
  rw [show (∫ a, g a * (hf2.toLp f : Q → ℂ) (q a) ∂dg) =
    ∫ a, g a * (hf2.toLp f : Q → ℂ) (Langlands.QuotientIntegration.leftQuotientMap Γ a) ∂dg
    from rfl, ← h1, MeasureTheory.L2.inner_def]
  have h2 : ∫ x, inner ℂ ((v : Q → ℂ) x) ((hf2.toLp f : Q → ℂ) x) ∂dq =
      ∫ x, starRingEnd ℂ (Langlands.QuotientIntegration.quotientAverage Γ dΓ f₀ x) * f x ∂dq := by
    refine integral_congr_ae ?_
    filter_upwards [hv, hf2.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply', hx1, hx2]
  rw [h2]
  let Fw : A → ℂ := fun a => g a * f (q a)
  have hFc : Continuous Fw :=
    g.continuous.mul (hfc.comp (LeftCosetSpace.continuous_mk Γ))
  have hFs : HasCompactSupport Fw := g.hasCompactSupport.mul_right
  have hW := hcompat.integral_formula Fw hFc hFs
  have hpt : ∀ x : Q, Langlands.QuotientIntegration.quotientAverage Γ dΓ Fw x =
      starRingEnd ℂ (Langlands.QuotientIntegration.quotientAverage Γ dΓ f₀ x) * f x := by
    intro x
    obtain ⟨a₀, rfl⟩ := LeftCosetSpace.mk_surjective Γ x
    change (∫ s : Γ, Fw (s.val * a₀) ∂dΓ) =
      starRingEnd ℂ (∫ s : Γ, f₀ (s.val * a₀) ∂dΓ) * f (q a₀)
    have hq : ∀ s : Γ, q (s.val * a₀) = q a₀ := fun s => LeftCosetSpace.mk_subgroup_mul Γ s a₀
    simp only [Fw, hq]
    rw [integral_mul_const, ← integral_conj]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    change g _ = starRingEnd ℂ (starRingEnd ℂ (g _))
    rw [Complex.conj_conj]
  exact (integral_congr_ae (Eventually.of_forall fun x => (hpt x).symm)).trans hW

omit [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant] in
include hi e hc in
/-- For any function `h` on `Q`, integrating `normOneSmoothingKernel K ρ` against `h ∘ q` gives
`∫ ρ` times the norm-one partial convolution of `h` at `1`. -/
theorem integral_normOneSmoothingKernel_mul (K : C_c(A, ℂ)) (ρ : C_c(Pos, ℂ)) (h : Q → ℂ) :
    ∫ a, normOneSmoothingKernel T i hi I e K ρ a * h (q a) ∂dg =
      (∫ b, ρ b ∂νP) * normOnePartialConvolution T i K h 1 := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveLocallyCompactSpace F T I e
  let := positiveSecondCountableTopology F T I e
  have hmp := measurePreserving_normOneDecomposition F H T i hi I e hc
  rw [← hmp.integral_comp (normOneDecomposition F H T i hi I e).measurableEmbedding]
  have hpt : ∀ p : Pos × A₁,
      normOneSmoothingKernel T i hi I e K ρ (normOneDecomposition F H T i hi I e p) *
          h (q (normOneDecomposition F H T i hi I e p)) =
        ρ p.1 * (starRingEnd ℂ (K ((p.2 : A)⁻¹)) * h (q (p.2 : A))) := by
    rintro ⟨b, n⟩
    simp only [normOneDecomposition_apply]
    have h1 : πP (ι₀ b * n) = b := positiveFactor_mul_normOne F H T i hi I e b n
    have h2 : (π₁ (ι₀ b * n) : A) = n := by
      rw [normOneFactor_val, h1, inv_mul_cancel_left]
    have h3 : q (ι₀ b * n) = q (n : A) :=
      LeftCosetSpace.mk_subgroup_mul _
        ⟨_, imageSubgroup_le_positiveRationalSubgroup F H T i ⟨b.val, b.property, rfl⟩⟩ _
    change ρ (πP (ι₀ b * n)) * starRingEnd ℂ (K ((π₁ (ι₀ b * n) : A)⁻¹)) * _ = _
    rw [h1, h2, h3, mul_assoc]
  simp_rw [hpt]
  let := normalizedPositiveHaarMeasure_sigmaFinite F H T i hi I e hc
  rw [integral_prod_mul (fun b => ρ b)
    (fun n : A₁ => starRingEnd ℂ (K ((n : A)⁻¹)) * h (q (n : A)))]
  congr 1
  unfold normOnePartialConvolution
  simp only [mul_one]

include hi e hc in
/-- The kernel vector paired with the `L²` class of a continuous square-integrable function `f`
on `Q` is the norm-one partial convolution of `f` itself at `1`. -/
theorem inner_normOneKernelVector_toLp (K : C_c(A, ℂ)) (f : Q → ℂ) (hfc : Continuous f)
    (hf2 : MemLp f 2 dq) :
    inner ℂ (normOneKernelVector T i hi I e hc K) (hf2.toLp f) =
      normOnePartialConvolution T i K f 1 := by
  obtain ⟨ρ, hρ⟩ := exists_positiveBump T i hi I e hc
  rw [inner_normOneKernelVector, (normOnePartialConvolution_one_eq_integral T i hi I e hc ρ hρ K
    (hf2.toLp f)).2, integral_mul_coeFn_toLp T i hi I e hc _ f hfc hf2,
    integral_normOneSmoothingKernel_mul T i hi I e hc, inv_mul_cancel_left₀ hρ]

include hi e hc in
/-- Norm-one partial convolutions of continuous square-integrable functions at any point are
inner products of kernel vectors of right translates with their `L²` classes. -/
theorem normOnePartialConvolution_eq_inner_toLp (K : C_c(A, ℂ)) (f : Q → ℂ)
    (hfc : Continuous f) (hf2 : MemLp f 2 dq) (y : A) :
    normOnePartialConvolution T i K f y =
      inner ℂ (normOneKernelVector T i hi I e hc (rightTranslateCc K y)) (hf2.toLp f) := by
  rw [inner_normOneKernelVector_toLp T i hi I e hc _ f hfc hf2]
  have h1 := normOnePartialConvolution_mul_right T i K f 1 y
  rw [one_mul] at h1
  exact h1

end Langlands.Global
