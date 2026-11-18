import Langlands.Global.RankinSelberg.RectangleTateCore
import Langlands.Global.Factors.RelativeWeilLocalHecke
import Langlands.Global.Factors.RelativeWeilAssemblyHecke
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.HeckeConductorSupport

/-! # Proof of `RectangleTateStatement`

The factorization of `RectangleTateCore` holds with constant one for the self-dual measures of
the components of a global additive character: the normalization hypothesis of
`RectangleTate.scalar_eq_one` is the Tamagawa normalization
`Hecke.mixedGaussianConst_mul_covolume_mul_prod_latticeMass` of the Hecke development, and the
local integrals at the places of `S` are moved from the completion topology to the canonical
topology of `padicField v`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RectangleTate

open Langlands.Global Langlands.Global.CompletionPadic

open scoped Classical

section Archimedean

variable {F : Type u} [Field F] [NumberField F]

/-- The product of the archimedean self-dual measures gives `D_∞` the mass
`κ covol(𝓞_F)`, with `κ = ∏_v √|a_v| ∏_w 2|a_w|`. -/
theorem archVolume (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ) :
    (Measure.pi fun v => (ArchimedeanLocal.realSelfDualMeasure (aR v)).measure).prod
        (Measure.pi fun w => (ArchimedeanLocal.complexSelfDualMeasure (aC w)).measure)
        (archDomain F) =
      ENNReal.ofReal (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun w => (aC w : ℂ)) *
        ZLattice.covolume (mixedEmbedding.idealLattice F (integerIdeal F))) := by
  have hR : (fun v => (ArchimedeanLocal.realSelfDualMeasure (aR v)).measure) =
      fun v => NNReal.sqrt ‖(aR v : ℝ)‖₊ • (volume : Measure ℝ) := rfl
  have hC : (fun w => (ArchimedeanLocal.complexSelfDualMeasure (aC w)).measure) =
      fun w => (‖(aC w : ℂ)‖₊ * 2) • (volume : Measure ℂ) := by
    funext w
    change ‖(aC w : ℂ)‖₊ • ((2 : ℝ≥0) • (volume : Measure ℂ)) = _
    rw [smul_smul]
  rw [hR, hC, pi_smul_eq (fun _ => (volume : Measure ℝ)) (fun v => NNReal.sqrt ‖(aR v : ℝ)‖₊),
    pi_smul_eq (fun _ => (volume : Measure ℂ)) (fun w => ‖(aC w : ℂ)‖₊ * 2),
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.smul_apply, smul_eq_mul]
  have hvol : (Measure.pi fun _ => (volume : Measure ℝ)).prod
      (Measure.pi fun _ => (volume : Measure ℂ)) =
      (volume : Measure (mixedEmbedding.mixedSpace F)) := rfl
  have hfin : volume (archDomain F) ≠ ∞ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain
    (mixedEmbedding.idealLattice F (integerIdeal F)) volume
    (mixedEmbedding.fundamentalDomain_idealLattice F (integerIdeal F))
  have hκ0 : 0 ≤ Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun w => (aC w : ℂ)) :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun _ _ => by positivity)
  have e1 : ∀ v, ENNReal.ofReal (Real.sqrt |(aR v : ℝ)|) = (NNReal.sqrt ‖(aR v : ℝ)‖₊ : ℝ≥0∞) :=
    fun v => by rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Real.norm_eq_abs]
  have e2 : ∀ w, ENNReal.ofReal (2 * ‖(aC w : ℂ)‖) = ((‖(aC w : ℂ)‖₊ * 2 : ℝ≥0) : ℝ≥0∞) :=
    fun w => by
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mul, coe_nnnorm, NNReal.coe_ofNat, mul_comm]
  have hκ : ENNReal.ofReal (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun w => (aC w : ℂ)))
      = (∏ v, (NNReal.sqrt ‖(aR v : ℝ)‖₊ : ℝ≥0∞)) *
        ∏ w, ((‖(aC w : ℂ)‖₊ * 2 : ℝ≥0) : ℝ≥0∞) := by
    unfold Hecke.mixedGaussianConst
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.sqrt_nonneg _),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
    simp only [e1, e2]
  rw [hvol, ENNReal.ofReal_mul hκ0, hκ, hcov, Measure.real, ENNReal.ofReal_toReal hfin]

end Archimedean

section Padic

variable {F : Type u} [Field F] [NumberField F]

/-- The p-adic rectangular integral for a Haar measure transported along an equality of
topologies is the integral for the original measure. -/
theorem padicRectIntegral_haarMeasureCongr (k m : ℕ) (v : FinitePlace F)
    {t : TopologicalSpace (FiniteCompletion F v)}
    (ht : t = (padicField v).canonicalTopologicalData.topology)
    (μ : @HarmonicAnalysis.AdditiveHaarMeasure (FiniteCompletion F v) _ t (@borel _ t))
    (f : Matrix (Fin k) (Fin m) (FiniteCompletion F v) → ℂ) :
    padicRectIntegral (padicField v) k m (LocalFactor.PadicAbelian.haarMeasureCongr ht μ) f =
      letI := t
      letI : MeasurableSpace (FiniteCompletion F v) := borel _
      ∫ y : Fin k → Fin m → FiniteCompletion F v, f y
        ∂(Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin m => μ.measure) := by
  subst ht
  rfl

end Padic

attribute [local instance] completionMeasurableSpace completionBorelSpace
  completionSecondCountable completionLocallyCompact

/-- **Proof of `RectangleTateStatement`** (Tate 1950, §4; Cogdell 2004, p.219). -/
theorem rectangleTateStatement : RectangleTateStatement.{u} := by
  intro F _ _ _ ψ hdiag S hsupp aR haR aC haC ψv hψv νv hνv k m hR hC hS
  set ψf : ∀ v : FinitePlace F, @HarmonicAnalysis.UnitaryAdditiveCharacter (padicField v).Carrier _
      (topologicalData v).topology :=
    fun v => FunctionalEquationComparison.RelativeWeilEngine.ofCanonicalCharacter v (ψv v)
    with hψf
  have hf : ∀ v, HeckeFunctionalEquation.IsFiniteAdditiveComponent ψ v (ψf v) :=
    fun v x => hψv v x
  let μ : ∀ v, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v) := fun v =>
    Classical.choice (FunctionalEquationComparison.RelativeWeilEngine.nonempty_selfDualHaar v (ψf v))
  let ν : ∀ v : S, Measure (FiniteCompletion F v.1) := fun v => (μ v.1).val.measure
  have hν : ∀ v : S, (ν v).IsAddHaarMeasure := fun v => (μ v.1).val.isAddHaar
  -- the additive conductors vanish outside `S`
  have hcond : ∀ v ∉ S, (topologicalData v).additiveConductor (ψf v) = 0 := by
    intro v hv
    obtain ⟨ψz, hz, hz0⟩ := hsupp v hv
    rw [← hz0]
    refine CuspidalPairFunctionalEquation.additiveConductor_congr
      (topologicalData_eq_canonicalTopologicalData v) (ψf v) ψz ?_
    refine DFunLike.ext _ _ fun x => ?_
    exact (hψv v x).trans (hz x).symm
  let n : FinitePlace F →₀ ℤ := Finsupp.onFinset S
    (fun v => (topologicalData v).additiveConductor (ψf v)) (fun v hv => by
      by_contra h
      exact hv (hcond v h))
  have hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v := fun _ => rfl
  have hnS : n.support ⊆ S := Finsupp.support_onFinset_subset
  -- Tamagawa normalization
  have htam := Hecke.mixedGaussianConst_mul_covolume_mul_prod_latticeMass
    (fun v => (aR v).ne_zero) (fun v => (aC v).ne_zero)
    (HeckeFunctionalEquation.additiveProductFormula_of_global ψ hdiag ψf hf aR haR aC haC)
    n hn μ 0 S (by simp) hnS
  set lm : FinitePlace F → ℝ := fun w =>
    Hecke.latticeMass (topologicalData w) (ψf w) (μ w) ((0 : FinitePlace F →₀ ℤ) w) with hlm_def
  have htam' : Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun w => (aC w : ℂ)) *
      ZLattice.covolume (mixedEmbedding.idealLattice F (integerIdeal F)) * ∏ v ∈ S, lm v = 1 :=
    htam
  have hset : ∀ v : S, ((topologicalData v.1).additiveLattice ((0 : FinitePlace F →₀ ℤ) v.1) :
      Set (FiniteCompletion F v.1)) = (v.1.adicCompletionIntegers F : Set _) := by
    intro v
    ext x
    simp only [Finsupp.coe_zero, Pi.zero_apply, SetLike.mem_coe]
    exact Hecke.mem_additiveLattice_zero_iff v.1 x
  have hlm : ∀ v : S, lm v.1 = (ν v (v.1.adicCompletionIntegers F)).toReal := by
    intro v
    show ((μ v.1).val.measure ((topologicalData v.1).additiveLattice _ : Set _)).toReal = _
    rw [hset v]
    rfl
  have hfin : ∀ v : S, ν v (v.1.adicCompletionIntegers F) ≠ ∞ :=
    fun v => (isCompact_adicCompletionIntegers F v.1).measure_lt_top.ne
  have hκ0 : 0 ≤ Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun w => (aC w : ℂ)) :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun _ _ => by positivity)
  have hnorm : (Measure.pi fun v => (ArchimedeanLocal.realSelfDualMeasure (aR v)).measure).prod
        (Measure.pi fun w => (ArchimedeanLocal.complexSelfDualMeasure (aC w)).measure)
        (archDomain F) * ∏ v, ν v (v.1.adicCompletionIntegers F) = 1 := by
    rw [archVolume aR aC]
    have hprod : ∏ v : S, ν v (v.1.adicCompletionIntegers F) = ∏ v : S, ENNReal.ofReal (lm v.1) :=
      Finset.prod_congr rfl fun v _ => by rw [hlm v, ENNReal.ofReal_toReal (hfin v)]
    rw [hprod, ← ENNReal.ofReal_prod_of_nonneg (fun v _ => by rw [hlm v]; exact ENNReal.toReal_nonneg),
      ← ENNReal.ofReal_mul (mul_nonneg hκ0 (ZLattice.covolume_pos _ _).le),
      Finset.prod_coe_sort S lm, htam', ENNReal.ofReal_one]
  -- assembly
  have hcore := integral_indicator_rect (S := S) (k := k) (m := m)
    (fun v => (ArchimedeanLocal.realSelfDualMeasure (aR v)).measure)
    (fun w => (ArchimedeanLocal.complexSelfDualMeasure (aC w)).measure) ν hR hC hS
  rw [scalar_eq_one (k := k) (m := m) _ _ _ hnorm, NNReal.coe_one, Complex.ofReal_one,
    one_mul] at hcore
  rw [hcore]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun v _ => ?_)
  have h1 := hνv v.1
  have h2 := LocalFactor.PadicAbelian.isSelfDualMeasure_haarMeasureCongr
    (topologicalData_eq_canonicalTopologicalData v.1) (ψf v.1) (μ v.1) (ψv v.1) rfl
  rw [Correspondence.eq_localSelfDualHaar _ (ψv v.1) _ h1,
    ← Correspondence.eq_localSelfDualHaar _ (ψv v.1) _ h2, padicRectIntegral_haarMeasureCongr]
  rfl

end Langlands.Global.RankinSelbergGlobal.RectangleTate
