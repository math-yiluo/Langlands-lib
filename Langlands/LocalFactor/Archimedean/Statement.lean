import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units

/-!
# Archimedean abelian local analysis

The objects in these targets are actual Schwartz functions, Haar measures,
Bochner integrals, continuous quasicharacters and Mathlib's Gamma factors.
Continuation uses the normal representative of a meromorphic function.
Functional equations are equalities of punctured germs, not values at poles.
-/

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap Topology

namespace Langlands.LocalFactor

/-- Classification of real and complex quasicharacters, with the complex
absolute value normalized as the square of the Euclidean norm. -/
def ArchimedeanQuasicharactersStatement : Prop :=
  (∀ χ : ContinuousMonoidHom ℝˣ ℂˣ,
    ∃! et : Fin 2 × ℂ, ∀ x : ℝˣ,
      (χ x : ℂ) = (((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ) ^ et.1.val *
        ((|(x : ℝ)| : ℝ) : ℂ) ^ et.2) ∧
  (∀ χ : ContinuousMonoidHom ℂˣ ℂˣ,
    ∃! mt : ℤ × ℂ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ mt.1 *
        (‖(z : ℂ)‖ : ℂ) ^ (2 * mt.2))

/-- Plus Fourier inversion, the inverse-character equation, and the unique
self-dual Haar measure for every nontrivial real additive character. -/
def RealArchimedeanFourierStatement : Prop :=
  let kernel (a x y : ℝ) : ℂ :=
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a * x * y : ℝ))
  let ft (a : ℝ) (μ : Measure ℝ) (f : ℝ → ℂ) (y : ℝ) :=
    ∫ x, kernel a x y * f x ∂μ
  let selfDual (a : ℝ) (μ : Measure ℝ) : Prop :=
    ∀ f : 𝓢(ℝ, ℂ),
      (∀ y, Integrable (fun x => kernel a x y * f x) μ) ∧
      (∃ g : 𝓢(ℝ, ℂ), ∀ y, g y = ft a μ f y) ∧
      (∀ y, Integrable (fun x => kernel a x y * ft a μ f x) μ) ∧
      (∀ y, ft a μ (ft a μ f) y = f (-y)) ∧
      (∀ y, ft (-a) μ (ft a μ f) y = f y)
  (∀ a : ℝˣ,
    let μ : Measure ℝ := ENNReal.ofReal (Real.sqrt |(a : ℝ)|) • volume
    μ.IsAddHaarMeasure ∧ μ.Regular ∧ selfDual a μ ∧
    ∀ ν : Measure ℝ, ν.IsAddHaarMeasure → ν.Regular → selfDual a ν → ν = μ) ∧
  (∀ (a : ℝˣ) (c : NNReal), 0 < c → ∀ (f : 𝓢(ℝ, ℂ)) (y : ℝ),
    ft a ((c : ENNReal) • volume) f y =
      (c : ℂ) * ft 1 volume f ((a : ℝ) * y)) ∧
  (∀ (a : ℝˣ) (c : NNReal), 0 < c →
    let μ : Measure ℝ := (c : ENNReal) • volume
    let ν : Measure ℝ := ENNReal.ofReal (|(a : ℝ)| / (c : ℝ)) • volume
    ν.IsAddHaarMeasure ∧ ν.Regular ∧
    (∀ (f : 𝓢(ℝ, ℂ)) (y : ℝ),
      Integrable (fun x => kernel (-(a : ℝ)) x y * ft a μ f x) ν ∧
      ft (-(a : ℝ)) ν (ft a μ f) y = f y) ∧
    (∀ ξ : Measure ℝ, ξ.IsAddHaarMeasure → ξ.Regular →
      (∀ (f : 𝓢(ℝ, ℂ)) (y : ℝ), ft (-(a : ℝ)) ξ (ft a μ f) y = f y) →
      ξ = ν))

/-- Complex trace Fourier inversion and the self-dual measure
`2 * norm(a)` times Euclidean area. -/
def ComplexArchimedeanFourierStatement : Prop :=
  let kernel (a x y : ℂ) : ℂ :=
    Complex.exp (4 * (Real.pi : ℂ) * Complex.I * ((a * x * y).re : ℂ))
  let ft (a : ℂ) (μ : Measure ℂ) (f : ℂ → ℂ) (y : ℂ) :=
    ∫ x, kernel a x y * f x ∂μ
  let selfDual (a : ℂ) (μ : Measure ℂ) : Prop :=
    ∀ f : 𝓢(ℂ, ℂ),
      (∀ y, Integrable (fun x => kernel a x y * f x) μ) ∧
      (∃ g : 𝓢(ℂ, ℂ), ∀ y, g y = ft a μ f y) ∧
      (∀ y, Integrable (fun x => kernel a x y * ft a μ f x) μ) ∧
      (∀ y, ft a μ (ft a μ f) y = f (-y)) ∧
      (∀ y, ft (-a) μ (ft a μ f) y = f y)
  (∀ a : ℂˣ,
    let μ : Measure ℂ := ENNReal.ofReal (2 * ‖(a : ℂ)‖) • volume
    μ.IsAddHaarMeasure ∧ μ.Regular ∧ selfDual a μ ∧
    ∀ ν : Measure ℂ, ν.IsAddHaarMeasure → ν.Regular → selfDual a ν → ν = μ) ∧
  (∀ (a : ℂˣ) (c : NNReal), 0 < c → ∀ (f : 𝓢(ℂ, ℂ)) (y : ℂ),
    ft a ((c : ENNReal) • ((2 : ENNReal) • volume)) f y =
      (c : ℂ) * ft 1 ((2 : ENNReal) • volume) f ((a : ℂ) * y)) ∧
  (∀ (a : ℂˣ) (c : NNReal), 0 < c →
    let μ : Measure ℂ := (c : ENNReal) • ((2 : ENNReal) • volume)
    let ν : Measure ℂ :=
      ENNReal.ofReal (‖(a : ℂ)‖ ^ 2 / (c : ℝ)) • ((2 : ENNReal) • volume)
    ν.IsAddHaarMeasure ∧ ν.Regular ∧
    (∀ (f : 𝓢(ℂ, ℂ)) (y : ℂ),
      Integrable (fun x => kernel (-(a : ℂ)) x y * ft a μ f x) ν ∧
      ft (-(a : ℂ)) ν (ft a μ f) y = f y) ∧
    (∀ ξ : Measure ℂ, ξ.IsAddHaarMeasure → ξ.Regular →
      (∀ (f : 𝓢(ℂ, ℂ)) (y : ℂ), ft (-(a : ℂ)) ξ (ft a μ f) y = f y) →
      ξ = ν))

/-- Real local zeta continuation and its local functional equation.
The epsilon scalar is explicit for every character and fixed Haar scaling.
The Gamma factor is separately normalized by its Gaussian zeta integral. -/
def RealArchimedeanTateStatement : Prop :=
  let integrand (f : ℝ → ℂ) (e : Fin 2) (t s : ℂ) (x : ℝ) :=
    if x = 0 then 0 else
      f x * ((x / |x| : ℝ) : ℂ) ^ e.val * ((|x| : ℝ) : ℂ) ^ (s + t - 1)
  let zeta (f : ℝ → ℂ) (e : Fin 2) (t s : ℂ) :=
    ∫ x, integrand f e t s x
  let extendsIntegral (Z : ℂ → ℂ) (f : ℝ → ℂ) (e : Fin 2) (t : ℂ) : Prop :=
    MeromorphicNFOn Z Set.univ ∧
      ∀ s, 0 < (s + t).re → Z s = zeta f e t s
  let ft (a : ℝ) (c : NNReal) (f : ℝ → ℂ) (y : ℝ) :=
    (c : ℂ) * ∫ x, Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (a * x * y : ℝ)) * f x
  let gaussian (e : Fin 2) (x : ℝ) : ℂ :=
    (x : ℂ) ^ e.val * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)
  (∀ (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t s : ℂ), 0 < (s + t).re →
    Integrable (integrand f e t s)) ∧
  (∀ (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t : ℂ),
    ∃! Z : ℂ → ℂ, extendsIntegral Z f e t) ∧
  (∀ (f : 𝓢(ℝ, ℂ)) (e : Fin 2) (t : ℂ)
    (a : ℝˣ) (c : NNReal), 0 < c →
    ∃ g : 𝓢(ℝ, ℂ), (∀ y, g y = ft a c f y) ∧
    ∀ (Z Y : ℂ → ℂ), extendsIntegral Z f e t → extendsIntegral Y g e (-t) →
      ∀ s₀ : ℂ,
        (fun s => Y (1 - s) / Complex.Gammaℝ (1 - s - t + e.val))
          =ᶠ[𝓝[≠] s₀]
        (fun s => (c : ℂ) * (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) ^ e.val *
          ((|(a : ℝ)| : ℝ) : ℂ) ^ (s + t - 1) * Complex.I ^ e.val *
          (Z s / Complex.Gammaℝ (s + t + e.val)))) ∧
  (∀ e : Fin 2,
    (∃ f : 𝓢(ℝ, ℂ), ∀ x, f x = gaussian e x) ∧
    (∀ x, ft 1 1 (gaussian e) x = Complex.I ^ e.val * gaussian e x) ∧
    (∀ t s : ℂ, 0 < (s + t).re →
      zeta (gaussian e) e t s = Complex.Gammaℝ (s + t + e.val)))

/-- Complex local zeta continuation, Gaussian Gamma normalization, and the
functional equation with trace character and fixed Haar scaling. -/
def ComplexArchimedeanTateStatement : Prop :=
  let μ : Measure ℂ := (2 : ENNReal) • volume
  let integrand (f : ℂ → ℂ) (m : ℤ) (t s z : ℂ) :=
    if z = 0 then 0 else
      f z * (z / (‖z‖ : ℂ)) ^ m * (‖z‖ : ℂ) ^ (2 * (s + t) - 2)
  let zeta (f : ℂ → ℂ) (m : ℤ) (t s : ℂ) :=
    ∫ z, integrand f m t s z ∂μ
  let extendsIntegral (Z : ℂ → ℂ) (f : ℂ → ℂ) (m : ℤ) (t : ℂ) : Prop :=
    MeromorphicNFOn Z Set.univ ∧
      ∀ s, 0 < (s + t).re → Z s = zeta f m t s
  let ft (a : ℂ) (c : NNReal) (f : ℂ → ℂ) (y : ℂ) :=
    (c : ℂ) * ∫ z, Complex.exp
      (4 * (Real.pi : ℂ) * Complex.I * ((a * z * y).re : ℂ)) * f z ∂μ
  let gaussian (m : ℤ) (z : ℂ) : ℂ :=
    (if 0 ≤ m then starRingEnd ℂ z ^ m.natAbs else z ^ m.natAbs) *
      Complex.exp (-2 * (Real.pi : ℂ) * (‖z‖ : ℂ) ^ 2) / (Real.pi : ℂ)
  (∀ (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t s : ℂ), 0 < (s + t).re →
    Integrable (integrand f m t s) μ) ∧
  (∀ (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t : ℂ),
    ∃! Z : ℂ → ℂ, extendsIntegral Z f m t) ∧
  (∀ (f : 𝓢(ℂ, ℂ)) (m : ℤ) (t : ℂ)
    (a : ℂˣ) (c : NNReal), 0 < c →
    ∃ g : 𝓢(ℂ, ℂ), (∀ y, g y = ft a c f y) ∧
    ∀ (Z Y : ℂ → ℂ), extendsIntegral Z f m t → extendsIntegral Y g (-m) (-t) →
      ∀ s₀ : ℂ,
        (fun s => Y (1 - s) /
          Complex.Gammaℂ (1 - s - t + (m.natAbs : ℂ) / 2))
          =ᶠ[𝓝[≠] s₀]
        (fun s => (c : ℂ) * ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ^ m *
          (‖(a : ℂ)‖ : ℂ) ^ (2 * (s + t - 1)) * Complex.I ^ m.natAbs *
          (Z s / Complex.Gammaℂ (s + t + (m.natAbs : ℂ) / 2)))) ∧
  (∀ m : ℤ,
    (∃ f : 𝓢(ℂ, ℂ), ∀ z, f z = gaussian m z) ∧
    (∀ z, ft 1 1 (gaussian m) z = Complex.I ^ m.natAbs * gaussian (-m) z) ∧
    (∀ t s : ℂ, 0 < (s + t).re →
      zeta (gaussian m) m t s =
        Complex.Gammaℂ (s + t + (m.natAbs : ℂ) / 2)))

/-- The actual archimedean abelian normalization and local-analysis targets. -/
def ArchimedeanAbelianLocalAnalysisStatement : Prop :=
  ArchimedeanQuasicharactersStatement ∧
  RealArchimedeanFourierStatement ∧
  ComplexArchimedeanFourierStatement ∧
  RealArchimedeanTateStatement ∧
  ComplexArchimedeanTateStatement

end Langlands.LocalFactor
