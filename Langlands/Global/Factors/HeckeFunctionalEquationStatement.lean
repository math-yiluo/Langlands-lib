import Langlands.Global.HeckeCharacter
import Langlands.Global.CompletionPadic
import Langlands.LocalFactor.Abelian.Padic
import Langlands.LocalFactor.ArchimedeanScaling
import Mathlib.Analysis.Meromorphic.Basic

/-!
# The global functional equation of Hecke L-functions

Tate (1979), Section 3.5, Theorem 3.5.3, in the abelian case `V = χ`.
The finite local factors are the published rank-one p-adic expressions over the
finite completions realized as p-adic fields. The archimedean factors use the
published presented real and complex characters. The additive character is a
global character of the adeles trivial on the diagonal; its local components are
read off at single places. Every local measure is self-dual for the local component.
See the paired Markdown for sources, normalizations and the choice of measures.
-/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField

variable {K : Type u} [Field K] [NumberField K]

/-- `ψv` is the restriction of the global additive character `ψ` to the finite
place `v`: `ψv x` is `ψ` of the adele with `x` at `v` and `0` elsewhere. -/
def IsFiniteAdditiveComponent (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (v : FinitePlace K)
    (ψv : @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
      (CompletionPadic.topologicalData v).topology) :
    Prop := by
  classical
  exact ∀ x : FiniteCompletion K v,
    ψv x = ψ (((0 : InfiniteAdeles K),
      (RestrictedProduct.single (fun w : FinitePlace K => w.adicCompletionIntegers K) v x :
        FiniteAdeles K)) : Adeles K)

/-- At a real place, the restriction of `ψ` is `x ↦ exp(2πi a x)` through the
real embedding of the completion. -/
def IsRealAdditiveComponent (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (v : InfinitePlace K) (hv : v.IsReal) (a : ℝˣ) : Prop := by
  classical
  exact ∀ x : InfiniteCompletion K v,
    ψ (((Pi.single v x : InfiniteAdeles K), (0 : FiniteAdeles K)) : Adeles K) =
      LocalFactor.Archimedean.realScaledCharacter a
        (InfinitePlace.Completion.ringEquivRealOfIsReal hv x)

/-- At a complex place, the restriction of `ψ` is `z ↦ exp(2πi Tr(a z))` through
Mathlib's chosen complex embedding of the completion. -/
def IsComplexAdditiveComponent (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K))
    (v : InfinitePlace K) (hv : v.IsComplex) (a : ℂˣ) : Prop := by
  classical
  exact ∀ x : InfiniteCompletion K v,
    ψ (((Pi.single v x : InfiniteAdeles K), (0 : FiniteAdeles K)) : Adeles K) =
      LocalFactor.Archimedean.complexScaledCharacter a
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv x)

/-- `d` presents the local character `η` at a real place, through the real
embedding of the completion. -/
def IsRealCharacterPresentation {v : InfinitePlace K} (hv : v.IsReal)
    (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) (d : LocalFactor.Archimedean.RealCharacterData) :
    Prop :=
  ∀ x : (InfiniteCompletion K v)ˣ,
    d.character (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMonoidHom x) =
      η x

/-- `d` presents the local character `η` at a complex place, through Mathlib's
chosen complex embedding of the completion. -/
def IsComplexCharacterPresentation {v : InfinitePlace K} (hv : v.IsComplex)
    (η : (InfiniteCompletion K v)ˣ →ₜ* ℂˣ) (d : LocalFactor.Archimedean.ComplexCharacterData) :
    Prop :=
  ∀ x : (InfiniteCompletion K v)ˣ,
    d.character
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toMonoidHom x) =
      η x

end HeckeFunctionalEquation

open HeckeFunctionalEquation

/-- Hecke's global functional equation in the form of Tate (1979), Theorem 3.5.3,
for `V = χ` a Hecke character and `ψ` a nontrivial character of the adeles trivial
on the diagonal, with self-dual local measures.

The first conjunct asserts that the local data exist. The second asserts, for
every choice of them, convergence of the Euler product in a right half-plane,
meromorphic continuation, almost-everywhere triviality of the local epsilon
factors, and the functional equation off a discrete set. -/
def HeckeGlobalFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ (K : Type u) [Field K] [NumberField K] (χ : HeckeCharacter K)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)),
    (∃ x : Adeles K, ψ x ≠ 1) → (∀ x : K, ψ (diagonal K x) = 1) →
    ((∀ v : FinitePlace K,
        ∃ ψv : @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
            (CompletionPadic.topologicalData v).topology,
          IsFiniteAdditiveComponent ψ v ψv ∧
            Nonempty (LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) ψv)) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal),
        (∃ a : ℝˣ, IsRealAdditiveComponent ψ v hv a) ∧
          ∃ d : LocalFactor.Archimedean.RealCharacterData,
            IsRealCharacterPresentation hv (χ.infiniteComponent v) d) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsComplex),
        (∃ a : ℂˣ, IsComplexAdditiveComponent ψ v hv a) ∧
          ∃ d : LocalFactor.Archimedean.ComplexCharacterData,
            IsComplexCharacterPresentation hv (χ.infiniteComponent v) d)) ∧
    ∀ (ψf : ∀ v : FinitePlace K,
        @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
          (CompletionPadic.topologicalData v).topology),
      (∀ v, IsFiniteAdditiveComponent ψ v (ψf v)) →
    ∀ (μ : ∀ v : FinitePlace K,
        LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v)),
    ∀ (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ),
      (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
    ∀ (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ),
      (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
    ∀ (dR dR' : {v : InfinitePlace K // v.IsReal} → LocalFactor.Archimedean.RealCharacterData),
      (∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v)) →
      (∀ v, IsRealCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dR' v)) →
    ∀ (dC dC' : {v : InfinitePlace K // v.IsComplex} →
        LocalFactor.Archimedean.ComplexCharacterData),
      (∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v)) →
      (∀ v, IsComplexCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dC' v)) →
    let finiteL (η : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) : ℂ :=
      LocalFactor.PadicAbelian.lFactor (CompletionPadic.topologicalData v) (η.finiteComponent v) s
    let finiteEpsilon (v : FinitePlace K) (s : ℂ) : ℂ :=
      letI := (CompletionPadic.topologicalData v).topology
      letI : MeasurableSpace (CompletionPadic.padicField v).Carrier := borel _
      LocalFactor.PadicAbelian.epsilon (CompletionPadic.topologicalData v) (χ.finiteComponent v)
        (ψf v) (μ v).val.measure s
    let infiniteDenominator (s : ℂ) : ℂ :=
      (∏ v, (dR v).lFactor.denominator s) * ∏ v, (dC v).lFactor.denominator s
    let dualInfiniteDenominator (s : ℂ) : ℂ :=
      (∏ v, (dR' v).lFactor.denominator s) * ∏ v, (dC' v).lFactor.denominator s
    let infiniteEpsilon (s : ℂ) : ℂ :=
      (∏ v, ((dR v).epsilon (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
        ∏ v, ((dC v).epsilon (aC v) ‖((aC v : ℂ))‖₊
          (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
    ∃ (σ : ℝ) (Λ Λdual : ℂ → ℂ) (S : Finset (FinitePlace K)),
      MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λdual Set.univ ∧
      (∀ s : ℂ, σ < s.re →
        HasProd (fun v => finiteL χ v s) (Λ s * infiniteDenominator s) ∧
          HasProd (fun v => finiteL χ⁻¹ v s) (Λdual s * dualInfiniteDenominator s)) ∧
      (∀ v ∉ S, ∀ s : ℂ, finiteEpsilon v s = 1) ∧
      ∀ᶠ s in Filter.codiscrete ℂ,
        Λ s = (∏ v ∈ S, finiteEpsilon v s) * infiniteEpsilon s * Λdual (1 - s)

end Langlands.Global
