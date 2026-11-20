import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # Normalizing a partial Whittaker integral from its pointwise product -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField MeasureTheory Set
open scoped Classical

namespace Langlands.Global.RankinSelbergGlobal

open CompletionPadic RankinSelberg

attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

/-- An entire normalized value of an ordinary integral with respect to a given L-factor. -/
structure OrdinaryIntegralNormalization (integral factor : ℂ → ℂ) where
  value : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ value univ
  eq_on_right : ∃ b : ℝ, ∀ s : ℂ, b < s.re → integral s = value s * factor s

namespace OrdinaryIntegralNormalization

/-- A finite product of ordinary local integrals has the product normalization. -/
def prod {ι : Type*} [Fintype ι] {I L : ι → ℂ → ℂ}
    (D : ∀ i, OrdinaryIntegralNormalization (I i) (L i)) :
    OrdinaryIntegralNormalization (fun s => ∏ i, I i s) (fun s => ∏ i, L i s) where
  value s := ∏ i, (D i).value s
  analytic s _ := Finset.analyticAt_fun_prod Finset.univ fun i _ => (D i).analytic s (mem_univ _)
  eq_on_right := by
    classical
    choose b hb using fun i => (D i).eq_on_right
    obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
    refine ⟨B, fun s hs => ?_⟩
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hb i s ((hB (Set.mem_range_self i)).trans_lt hs)

end OrdinaryIntegralNormalization

variable {F : Type u} [Field F] [NumberField F] {t : ℕ}
  {S : Finset (FinitePlace F)}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

/-- Integrate an ordinary pointwise kernel factorization against the actual partial quotient
measure. The normalizing value is the product of the local values times the two nonzero
constants from the pointwise factorization and the quotient measure comparison. -/
theorem exists_normalization_of_semilocal_pointwise_product
    (DR : RP → ArchimedeanLocal.RealQuotientMeasureData t)
    (DC : CP → ArchimedeanLocal.ComplexQuotientMeasureData t)
    (μS : ∀ v : S, PadicQuotientMeasure (padicField v.1) t)
    (hμ : ∀ v : S, IsCompatiblePadicQuotientMeasure (padicField v.1) (μS v))
    (I : ℂ → WhittakerQuotient F (t + 1) → ℂ) {κ : ℂ} (hκ : κ ≠ 0)
    (fR : RP → ℂ → LeftUnipotentQuotient t ℝ → ℂ)
    (fC : CP → ℂ → LeftUnipotentQuotient t ℂ → ℂ)
    (fS : ∀ v : S, ℂ → LeftUnipotentQuotient t (padicField v.1).Carrier → ℂ)
    (hI : ∃ b : ℝ, ∀ s : ℂ, b < s.re → ∀ q ∈ unipotentIntegralClasses F (t + 1) S,
      I s q = κ * ((∏ v, fR v s (realQuotientProjection F t v q)) *
        (∏ w, fC w s (complexQuotientProjection F t w q)) *
        ∏ v : S, fS v s (finiteQuotientProjection F t v.1 q)))
    {LR : RP → ℂ → ℂ} {LC : CP → ℂ → ℂ} {LS : S → ℂ → ℂ}
    (NR : ∀ v, OrdinaryIntegralNormalization (fun s => ∫ y, fR v s y ∂(DR v).measure) (LR v))
    (NC : ∀ v, OrdinaryIntegralNormalization (fun s => ∫ y, fC v s y ∂(DC v).measure) (LC v))
    (NS : ∀ v, OrdinaryIntegralNormalization
      (fun s => padicQuotientIntegral (padicField v.1) (μS v) (fS v s)) (LS v)) :
    ∃ K : ℂ, K ≠ 0 ∧
      ∃ N : OrdinaryIntegralNormalization
        (fun s => ∫ q in unipotentIntegralClasses F (t + 1) S, I s q
          ∂whittakerQuotientMeasure F (t + 1))
        (fun s => ((∏ v, LR v s) * ∏ w, LC w s) * ∏ v : S, LS v s),
        ∀ s, N.value s = K * ((∏ v, (NR v).value s) * (∏ w, (NC w).value s) *
          ∏ v : S, (NS v).value s) := by
  classical
  obtain ⟨C, hC, hprod⟩ := UnipotentClass.unipotentClassProductStatement F t S DR DC μS hμ
  let realFactors := OrdinaryIntegralNormalization.prod NR
  let complexFactors := OrdinaryIntegralNormalization.prod NC
  let finiteFactors := OrdinaryIntegralNormalization.prod NS
  refine ⟨κ * C, mul_ne_zero hκ hC, ⟨fun s => κ * C * (realFactors.value s * complexFactors.value s * finiteFactors.value s),
    fun s hs => analyticAt_const.fun_mul
      (((realFactors.analytic s hs).fun_mul (complexFactors.analytic s hs)).fun_mul
        (finiteFactors.analytic s hs)), ?_⟩,
    fun _ => rfl⟩
  obtain ⟨b, hb⟩ := hI
  obtain ⟨br, hbr⟩ := realFactors.eq_on_right
  obtain ⟨bc, hbc⟩ := complexFactors.eq_on_right
  obtain ⟨bf, hbf⟩ := finiteFactors.eq_on_right
  refine ⟨max (max b br) (max bc bf), fun s hs => ?_⟩
  have hPoint := hb s ((le_max_left b br).trans_lt ((le_max_left _ _).trans_lt hs))
  have hR := hbr s ((le_max_right b br).trans_lt ((le_max_left _ _).trans_lt hs))
  have hCmp := hbc s ((le_max_left bc bf).trans_lt ((le_max_right _ _).trans_lt hs))
  have hF := hbf s ((le_max_right bc bf).trans_lt ((le_max_right _ _).trans_lt hs))
  rw [setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) S) hPoint,
    integral_const_mul, hprod, hR, hCmp, hF]
  ring

end Langlands.Global.RankinSelbergGlobal
