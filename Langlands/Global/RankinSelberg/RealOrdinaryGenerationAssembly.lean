import Langlands.Global.RankinSelberg.RealOrdinaryPointwiseCoverage
import Langlands.Global.RankinSelberg.RealOrdinaryPolynomialReduction
import Langlands.Global.RankinSelberg.RealUnequalSpectralMultiplication

/-! # Assembly of real ordinary normalized generation -/

noncomputable section

open Langlands.LocalFactor.Archimedean Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal
open RealJacquet (IsRealCharacterList)
open RealEqualPolynomialGeneration
open RealUnequalSpectralMultiplication (realUnequalFiniteSumFromPolynomials)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

/-- Standard polynomial Gaussian Schwartz rows are dense in each positive dimension. -/
def RealGaussianRowsDenseStatement : Prop :=
  ∀ r : ℕ, Dense {Φ : 𝓢(Fin (r + 1) → ℝ, ℂ) | IsGaussianPolynomialRow Real.pi Φ}

private theorem gaussianEqualCoverage (hO : RealOrdinaryNormalizedContinuationStatement)
    (hDensity : RealGaussianRowsDenseStatement) (r : ℕ) (ds es : List RealBlock)
    (hd : realRank ds = r + 1) (he : realRank es = r + 1) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (hCover : HasCoveringOrdinaryNormalizations (realOrdinaryEqualTest r ds es a D)
      (realPairLFactor ds es)) :
    HasCoveringOrdinaryNormalizations (gaussianEqualIntegral r ds es a Real.pi D)
      (realPairLFactor ds es) := by
  intro s
  obtain ⟨⟨W, V, Φ⟩, N, hN⟩ := hCover s
  let j : {Φ : 𝓢(Fin (r + 1) → ℝ, ℂ) // IsGaussianPolynomialRow Real.pi Φ} →
      𝓢(Fin (r + 1) → ℝ, ℂ) := Subtype.val
  have hDense : Dense (Submodule.span ℂ (range j) : Set 𝓢(Fin (r + 1) → ℝ, ℂ)) :=
    (hDensity r).mono fun Φ hΦ => Submodule.subset_span ⟨⟨Φ, hΦ⟩, rfl⟩
  have hL := realOrdinaryEqualRowEvaluation hO r ds es hd he a D W V
  obtain ⟨Ψ, M, hM⟩ := hL.detects_dense_span (fun Ψ => hO.2 r ds es hd he a D (W, V, Ψ)) j
    hDense s ⟨Φ, N, hN⟩
  exact ⟨(W, V, Ψ), M, hM⟩

/-- Exact real continuation, the polynomial calculation for character lists and Gaussian
row density suffice for the ordinary normalized generation statement. -/
def RealOrdinaryGenerationAssemblyStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement → RealOrdinaryPolynomialStatement IsRealCharacterList →
    RealGaussianRowsDenseStatement → RealOrdinaryNormalizedGenerationStatement

theorem realOrdinaryGenerationAssembly : RealOrdinaryGenerationAssemblyStatement := by
  intro hO hChar hDensity
  obtain ⟨hUnequal, hEqual⟩ := realOrdinaryPointwiseCoverage hO
  obtain ⟨hAdjPoly, hEqPoly⟩ := realOrdinaryPolynomialReduction hO hChar
  constructor
  · intro r t h ds es hd he hdI heI a D _ _
    have hCover := hUnequal r t h ds es hd he hdI heI a D
    refine ⟨hCover, fun hAdj ha => ?_⟩
    subst r
    refine realUnequalFiniteSumFromPolynomials (t + 1) t h ds es hdI heI a D (fun i => ?_) hCover
    obtain ⟨N, P, hP⟩ := hAdjPoly t ds es trivial trivial hd he a ha D i
    exact ⟨P, N, congrFun hP⟩
  · intro r ds es hd he hdI heI a D _ _
    have hCover := hEqual r ds es hd he hdI heI a D
    refine ⟨hCover, fun ha => ?_⟩
    refine realEqualFiniteSumFromPolynomials r ds es hdI heI a Real.pi D (fun i => ?_)
      (gaussianEqualCoverage hO hDensity r ds es hd he a D hCover)
    obtain ⟨N, P, hP⟩ := hEqPoly r ds es trivial trivial hd he a ha D i
    exact ⟨P, N, congrFun hP⟩

end Langlands.Global.RankinSelbergGlobal
