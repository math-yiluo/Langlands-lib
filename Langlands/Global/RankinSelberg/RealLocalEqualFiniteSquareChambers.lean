import Langlands.Global.RankinSelberg.RealLocalEqualFiniteSquareNormalized
import Langlands.Global.RankinSelberg.RealLocalEqualChamberTrace

/-! # The real finite normalized traces on common convergence chambers -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealUniformWhittakerDual (dualCharacterBlocks realUniformWhittakerCharacterDual)
open RealLocalWhittaker (regularFunctions)

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedAddCommGroup (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedSpace ℂ (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedSpace

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "U" => GeneralLinear.upperUnipotent (t + 2) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "gap" => Nat.lt_succ_self t
local notation "ιT" => GeneralLinear.inverseTranspose (t + 2) ℝ

/-- For uniform Whittaker coefficients `W` and `V` with opposite characters, the real
unfolded kernel is absolutely integrable for every parity, every square Schwartz test and
all `(z, s)` in one product of right half-planes. -/
theorem exists_uniformModel_equalKernel_chamber (D : RealQuotientMeasureData t)
    (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ) (ds es : List RealBlock) {W : G → ℂ}
    {V : H → ℂ} (hW : W ∈ realUniformWhittakerModel t ds a)
    (hV : V ∈ realUniformWhittakerModel (t + 1) es (-a)) :
    ∃ τ σ : ℝ, ∀ (e : Fin 2) (Ψ : 𝓢(Y, ℂ)) (z s : ℂ), τ < z.re → σ < s.re →
      Integrable (equalUnfoldedKernel (charData e z) Ψ W V s) (D.measure.prod D'.groupHaar) := by
  obtain ⟨hWreg, hWgrowth⟩ := realUniformWhittakerRegularity t ds a W hW
  obtain ⟨hVreg, hVgrowth⟩ := realUniformWhittakerRegularity (t + 1) es (-a) V hV
  have hWr : W ∈ regularFunctions t a := hWreg []
  have hVr : V ∈ regularFunctions (t + 1) (-a) := hVreg []
  have hWg : RealEqualConvergence.HasGauge W :=
    RealWhittakerGauge.exists_gauge_bound hWreg hWgrowth
  have hVg : RealEqualConvergence.HasGauge V :=
    RealWhittakerGauge.exists_gauge_bound hVreg hVgrowth
  have hVu : ∀ (u : U) (g : H), ‖V (u.val * g)‖ = ‖V g‖ := by
    intro u g
    rw [hVr.1 u.val u.2 g, norm_mul, RealUnequalPairConvergence.norm_realWhittakerCharacter,
      one_mul]
  obtain ⟨ρ, σ, hJ⟩ := realLocalEqualJointIntegrability D D' W V hWr.2.1.continuous
    hVr.2.1.continuous hWg hVg hVu
  refine ⟨ρ, σ, fun e Ψ z s hz hs => ?_⟩
  obtain ⟨k, C, _, h⟩ := hJ z.re s.re hz.le hs
  exact (h Ψ (charData e z) s rfl rfl).1

variable (t) in
/-- The matrix input of `RealLocalEqualFiniteSquareNormalizedStatement` for one square test
`Ψ`: for every bounded linear form `ℓ` on the smooth principal series, with matrix coefficient
`b_ℓ(g) = ℓ(π(g) f)`, the weighted matrix integrands of `Ψ` with `b_ℓ` and of the Fourier test
with `b_ℓ ∘ (inverse transpose)` are integrable on a right half-plane, and the two matrix
integrals have an entire normalization with strip growth. -/
def RealMatrixCoefficientNormalizedGrowth (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ)
    (e : Fin 2) (es : List RealBlock) (f : Automorphic.realStandardKFinite (t + 2) es)
    (Ψ : 𝓢(Y, ℂ)) (us vs usd vsd : List RealBlock) (bM : ℝˣ) (cM : ℝ≥0) (hcM : 0 < cM)
    (signM : ℂ) : Prop :=
  ∀ ℓ, RealPrincipalSeries.HasCompactDerivativeBound (t + 1) (RealPrincipalSeries.expand es) ℓ →
    (∃ β : ℝ, ∀ w : ℂ, β < w.re →
      Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g *
        realStandardMatrixCoefficient es ℓ f g) D'.groupHaar ∧
      Integrable (fun g => realWeightedMatrixTest (charData e 0)
        (realRectangularSchwartzFourier (-a) Ψ) (w + (m : ℂ) / 2) g *
        realStandardMatrixCoefficient es ℓ f (ιT g)) D'.groupHaar) ∧
    HasRealPairNormalizedGrowth us vs usd vsd bM cM hcM signM
      (realWeightedMatrixIntegral D'.groupHaar e Ψ (realStandardMatrixCoefficient es ℓ f))
      (realWeightedMatrixIntegral D'.groupHaar e (realRectangularSchwartzFourier (-a) Ψ)
        (realStandardMatrixCoefficient es ℓ f ∘ ιT))

variable (t) in
/-- The finite square normalization of `RealLocalEqualFiniteSquareNormalizedStatement` holds on
two chambers chosen before the square test: the primal chamber `τ < Re z`, `σ < Re s` and the
dual chamber `τ_d < Re(-z)`, `σ_d < Re s`. On these chambers the primal and dual unfolded
kernels are absolutely integrable for every square Schwartz test. -/
def RealLocalEqualFiniteSquareChambersStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ) (e : Fin 2)
    (cs fs : List RealCharacterData), cs.length = t + 1 → fs.length = t + 2 →
  ∀ (W : G → ℂ), W ∈ realUniformWhittakerModel t (cs.map RealBlock.character) a →
  ∀ (B : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
    IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B →
    (∃ L : DerivativeSmoothVectors (matrixModel ℝ (t + 2))
        (RealStandardCompactBanach.representation (n := t + 2) (fs.map RealBlock.character)) →L[ℂ] ℂ,
      RealStandardCompactBanach.IsWhittakerStandardEvaluation (fs.map RealBlock.character) (-a) B L) →
  ∀ (f : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character))
    (xs ys xsd ysd : List RealBlock) (bA : ℝˣ) (cA : ℝ≥0) (hcA : 0 < cA) (signA : ℂ),
    (∀ V ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a),
      HasRealPairNormalizedGrowth xs ys xsd ysd bA cA hcA signA
        (realUnequalIntegral gap D V W) (realUnequalDualIntegral gap (-a) D V W)) →
  ∀ (us vs usd vsd : List RealBlock) (bM : ℝˣ) (cM : ℝ≥0) (hcM : 0 < cM) (signM : ℂ),
    ∃ τ σ τd σd : ℝ,
      (∀ (Ψ : 𝓢(Y, ℂ)) (z s : ℂ), τ < z.re → σ < s.re →
        Integrable (equalUnfoldedKernel (charData e z) Ψ W (B f) s)
          (D.measure.prod D'.groupHaar)) ∧
      (∀ (Ψ : 𝓢(Y, ℂ)) (z s : ℂ), τd < (-z).re → σd < s.re →
        Integrable (equalUnfoldedKernel (charData e (-z)) Ψ (ArchimedeanLocal.dualFunction (t + 1) W)
          (ArchimedeanLocal.dualFunction (t + 2) (B f)) s) (D.measure.prod D'.groupHaar)) ∧
      ∀ Ψ : 𝓢(Y, ℂ), FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ (t + 2) =>
          fun X : Y => Ψ (k.val⁻¹.val * X))) →
        RealMatrixCoefficientNormalizedGrowth t D' a e (fs.map RealBlock.character) f Ψ
          us vs usd vsd bM cM hcM signM →
        ∃ F Fd : ℂ × ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Fd ∧
          (∀ z : ℂ, HasStripExponentialGrowth (fun s => F (z, s))) ∧
          (∀ v : ℂ, HasStripExponentialGrowth (fun s => F (v + s, s))) ∧
          (∀ z : ℂ, HasStripExponentialGrowth (fun s => Fd (z, s))) ∧
          (∀ v : ℂ, HasStripExponentialGrowth (fun s => Fd (v + s, s))) ∧
          (∀ z s : ℂ, τ < z.re → σ < s.re →
            F (z, s) = (realPairLFactor xs ys).denominator s *
              (realPairLFactor us vs).denominator (s + z) *
              ∫ p, equalUnfoldedKernel (charData e z) Ψ W (B f) s p
                ∂(D.measure.prod D'.groupHaar)) ∧
          (∀ z s : ℂ, τd < (-z).re → σd < s.re →
            Fd (z, s) = (realPairLFactor xsd ysd).denominator s *
              (realPairLFactor usd vsd).denominator (s - z) *
              ∫ p, equalUnfoldedKernel (charData e (-z)) (realRectangularSchwartzFourier (-a) Ψ)
                (ArchimedeanLocal.dualFunction (t + 1) W)
                (ArchimedeanLocal.dualFunction (t + 2) (B f)) s p
                  ∂(D.measure.prod D'.groupHaar)) ∧
          ∀ z s : ℂ, Fd (z, 1 - s) = signA * (realPairEpsilon xs ys bA cA hcA s : ℂ) *
            (signM * (realPairEpsilon us vs bM cM hcM (s + z) : ℂ)) * F (z, s)

set_option maxHeartbeats 800000 in
theorem realLocalEqualFiniteSquareChambers : RealLocalEqualFiniteSquareChambersStatement t := by
  intro D D' a e cs fs hcs hfs W hW B hB hL f xs ys xsd ysd bA cA hcA signA hAdj
    us vs usd vsd bM cM hcM signM
  have hV : B f ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hWd := realUniformWhittakerCharacterDual t cs hcs a W hW
  have hVd := realUniformWhittakerCharacterDual (t + 1) fs hfs (-a) (B f) hV
  obtain ⟨τ, σ, hI⟩ := exists_uniformModel_equalKernel_chamber D D' a
    (cs.map RealBlock.character) (fs.map RealBlock.character) hW hV
  obtain ⟨τd, σd, hId⟩ := exists_uniformModel_equalKernel_chamber D D' (-a)
    (dualCharacterBlocks cs) (dualCharacterBlocks fs) hWd hVd
  refine ⟨τ, σ, τd, σd, fun Ψ z s hz hs => hI e Ψ z s hz hs,
    fun Ψ z s hz hs => hId e Ψ (-z) s hz hs, fun Ψ hfin hMat => ?_⟩
  obtain ⟨F, Fd, hF, hFd, g₁, g₂, g₃, g₄, hDeep, hDeepd, hRef⟩ :=
    realLocalEqualFiniteSquareNormalized D D' a e cs fs hcs hfs W hW B hB hL f Ψ hfin
      xs ys xsd ysd bA cA hcA signA hAdj us vs usd vsd bM cM hcM signM hMat
  let N (p : ℂ × ℂ) : ℂ :=
    (realPairLFactor xs ys).denominator p.2 * (realPairLFactor us vs).denominator (p.2 + p.1)
  have hN : Differentiable ℂ N :=
    ((realPairLFactor xs ys).entire.comp differentiable_snd).mul
      ((realPairLFactor us vs).entire.comp (differentiable_snd.add differentiable_fst))
  let Gd (p : ℂ × ℂ) : ℂ := Fd (-p.1, p.2)
  have hGd : Differentiable ℂ Gd := hFd.comp (differentiable_fst.neg.prodMk differentiable_snd)
  let Nd (p : ℂ × ℂ) : ℂ :=
    (realPairLFactor xsd ysd).denominator p.2 * (realPairLFactor usd vsd).denominator (p.2 + p.1)
  have hNd : Differentiable ℂ Nd :=
    ((realPairLFactor xsd ysd).entire.comp differentiable_snd).mul
      ((realPairLFactor usd vsd).entire.comp (differentiable_snd.add differentiable_fst))
  have hDeepd' : ∃ τ' σ' : ℝ, ∀ z s : ℂ, τ' < z.re → σ' < s.re →
      Gd (z, s) = Nd (z, s) *
        ∫ q, equalUnfoldedKernel (charData e z) (realRectangularSchwartzFourier (-a) Ψ)
          (ArchimedeanLocal.dualFunction (t + 1) W) (ArchimedeanLocal.dualFunction (t + 2) (B f)) s q
            ∂(D.measure.prod D'.groupHaar) := by
    obtain ⟨τ', σ', h⟩ := hDeepd
    refine ⟨τ', σ', fun z s hz hs => ?_⟩
    have h' := h (-z) s (by rwa [neg_neg]) hs
    rw [neg_neg, sub_neg_eq_add] at h'
    exact h'
  refine ⟨F, Fd, hF, hFd, g₁, g₂, g₃, g₄, fun z s hz hs => ?_, fun z s hz hs => ?_, hRef⟩
  · exact eq_mul_integral_equalUnfoldedKernel_of_deep D D' e Ψ W (B f) hF hN
      (fun z s hz hs => hI e Ψ z s hz hs) hDeep z s hz hs
  · have h := eq_mul_integral_equalUnfoldedKernel_of_deep D D' e
      (realRectangularSchwartzFourier (-a) Ψ) (ArchimedeanLocal.dualFunction (t + 1) W)
      (ArchimedeanLocal.dualFunction (t + 2) (B f)) hGd hNd
      (fun z s hz hs => hId e _ z s hz hs) hDeepd' (-z) s hz hs
    simp only [Gd, Nd, neg_neg, ← sub_eq_add_neg] at h
    exact h

end Langlands.Global.RankinSelbergGlobal.RealGodement
