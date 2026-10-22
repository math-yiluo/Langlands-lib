import Langlands.LocalFactor.Abelian.Padic

/-!
# Abelian local analysis over a finite p-adic field

The local aliases below refer to concrete callable expressions.
No epsilon system, meromorphic continuation or Fourier theorem is assumed.
The shared harmonic-analysis definitions supply the actual characters, test
functions, measures and plus Fourier integral. The paired Markdown explains
the conductor conventions, the measure dependence and evaluation at poles.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.LocalFactor

universe u

/-- Tate's abelian local analysis with actual valuation, residue cardinality,
characters, Haar measures, integrals, Euler factors and Gauss expressions.
The normalized meromorphic representatives are compared through punctured
germs at singular points. This is a theorem target, not a theorem proof. -/
def PadicAbelianLocalAnalysisStatement : Prop := by
  classical
  exact
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  let q : ℝ := T.residueCardinality
  let O : Set F.Carrier := PadicAbelian.integerRing T
  let U : Set F.Carrier := PadicAbelian.integralUnits T
  let Q (s : ℂ) := PadicAbelian.spectralVariable T s
  let chi0 (χ : HarmonicAnalysis.Quasicharacter F.Carrier) (x : F.Carrier) : ℂ :=
    PadicAbelian.characterExtension T χ x
  let unitLevel (a : ℕ) (v : F.Carrierˣ) : Prop :=
    PadicAbelian.unitLevel T a v
  let conductor (χ : HarmonicAnalysis.Quasicharacter F.Carrier) (a : ℕ) : Prop :=
    PadicAbelian.ConductorAt T χ a
  let addConductor (ψ : AddChar F.Carrier Circle) (n : ℤ) : Prop :=
    PadicAbelian.AdditiveConductorAt T ψ n
  let lFactor (π : F.Carrierˣ) (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (a : ℕ) (s : ℂ) : ℂ :=
    PadicAbelian.lFactorAt T π χ a s
  let regular (π : F.Carrierˣ) (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (a : ℕ) (s : ℂ) : Prop :=
    PadicAbelian.RegularPoint T π χ a s
  let converges (π : F.Carrierˣ) (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (s : ℂ) : Prop :=
    PadicAbelian.ConvergesAt T π χ s
  let integrand (f : F.Carrier → ℂ) (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (s : ℂ) (x : F.Carrier) : ℂ :=
    PadicAbelian.zetaIntegrand T f χ s x
  let zeta (μ : Measure F.Carrier) (f : F.Carrier → ℂ)
      (χ : HarmonicAnalysis.Quasicharacter F.Carrier) (s : ℂ) : ℂ :=
    PadicAbelian.zeta T μ f χ s
  let extendsIntegral (π : F.Carrierˣ) (μ : Measure F.Carrier)
      (f : F.Carrier → ℂ) (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (Z : ℂ → ℂ) : Prop :=
    PadicAbelian.ExtendsIntegral T π μ f χ Z
  let laurent (A : ℤ →₀ ℂ) (s : ℂ) : ℂ :=
    PadicAbelian.laurentEvaluation T A s
  let gaussIntegrand (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (ψ : AddChar F.Carrier Circle) (s : ℂ) (x : F.Carrier) : ℂ :=
    PadicAbelian.gaussIntegrand T χ ψ s x
  let shell (d : ℤ) : Set F.Carrier := PadicAbelian.gaussShell T d
  let epsilon (π : F.Carrierˣ) (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (ψ : AddChar F.Carrier Circle) (μ : Measure F.Carrier)
      (a : ℕ) (n : ℤ) (s : ℂ) : ℂ :=
    PadicAbelian.epsilonAt T π χ ψ μ a n s
  (∃ π : F.Carrierˣ, T.ord (π : F.Carrier) = 1) ∧
  (∀ χ : HarmonicAnalysis.Quasicharacter F.Carrier,
    IsOpen {v : F.Carrierˣ | χ v = 1} ∧
    IsLocallyConstant (fun v : F.Carrierˣ => χ v) ∧
    (∀ v : F.Carrierˣ, unitLevel 0 v → ‖(χ v : ℂ)‖ = 1) ∧
    (Set.range (fun v : {v : F.Carrierˣ // unitLevel 0 v} => χ v.val)).Finite ∧
    (∃! a : ℕ, conductor χ a)) ∧
  (∀ (χ η : HarmonicAnalysis.Quasicharacter F.Carrier) (a b : ℕ),
    conductor χ a → conductor η b →
    conductor χ⁻¹ a ∧
    (∃ c : ℕ, conductor (χ * η) c ∧ c ≤ max a b) ∧
    (a ≠ b → conductor (χ * η) (max a b)) ∧
    (b = 0 → conductor (χ * η) a)) ∧
  ∀ (π : F.Carrierˣ), T.ord (π : F.Carrier) = 1 →
  ∀ (χ : HarmonicAnalysis.Quasicharacter F.Carrier) (a : ℕ), conductor χ a →
  ∀ (μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier),
  (0 < (μ.measure O).toReal ∧ 0 < (μ.measure U).toReal ∧
    (μ.measure U).toReal = (1 - q⁻¹) * (μ.measure O).toReal) ∧
  (MeromorphicNFOn (lFactor π χ a) Set.univ ∧
    ∀ s, regular π χ a s → lFactor π χ a s ≠ 0) ∧
  (∀ f : HarmonicAnalysis.SchwartzBruhat F.Carrier,
    (∀ s, converges π χ s → Integrable (integrand f χ s) μ.measure) ∧
    DifferentiableOn ℂ (zeta μ.measure f χ) {s | converges π χ s} ∧
    (∃! Z : ℂ → ℂ, extendsIntegral π μ.measure f χ Z) ∧
    (∀ Z : ℂ → ℂ, extendsIntegral π μ.measure f χ Z →
      ∃! A : ℤ →₀ ℂ,
        (∀ s₀ : ℂ, Z =ᶠ[𝓝[≠] s₀] (fun s => lFactor π χ a s * laurent A s)) ∧
        (∀ s, regular π χ a s → Z s = lFactor π χ a s * laurent A s))) ∧
  (let test : F.Carrier → ℂ :=
      if a = 0 then O.indicator (fun _ => (1 : ℂ)) else
        U.indicator (fun x => (chi0 χ x)⁻¹)
   (∃ f : HarmonicAnalysis.SchwartzBruhat F.Carrier, ∀ x, f x = test x) ∧
   ∀ s, converges π χ s →
     zeta μ.measure test χ s = (μ.measure U).toReal * lFactor π χ a s) ∧
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (n : ℤ),
    addConductor ψ.toAddChar n →
  (∀ s : ℂ,
    IntegrableOn (gaussIntegrand χ ψ.toAddChar s) (shell (n + a)) μ.measure ∧
    epsilon π χ ψ.toAddChar μ.measure a n s ≠ 0) ∧
  Differentiable ℂ (epsilon π χ ψ.toAddChar μ.measure a n) ∧
  (∀ s : ℂ,
    epsilon π χ ψ.toAddChar μ.measure a n s =
      epsilon π χ ψ.toAddChar μ.measure a n 0 *
        Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * s * (Real.log q : ℂ))) ∧
  (∀ s : ℂ,
    epsilon π χ ψ.toAddChar μ.measure a n s =
      epsilon π χ ψ.toAddChar μ.measure a n (1 / 2) *
        Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (s - 1 / 2) *
          (Real.log q : ℂ))) ∧
  (∀ (ρ : F.Carrierˣ), T.ord (ρ : F.Carrier) = 1 → ∀ s : ℂ,
    lFactor ρ χ a s = lFactor π χ a s ∧
    epsilon ρ χ ψ.toAddChar μ.measure a n s =
      epsilon π χ ψ.toAddChar μ.measure a n s) ∧
  (∀ c : F.Carrierˣ, T.ord (c : F.Carrier) = n + a → ∀ s : ℂ,
    epsilon π χ ψ.toAddChar μ.measure a n s =
      if a = 0 then (χ c : ℂ) *
        Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (c : F.Carrier)) : ℂ)) *
        (μ.measure O).toReal
      else ∫ x in (fun v => (c⁻¹ : F.Carrierˣ) * v) '' U,
        gaussIntegrand χ ψ.toAddChar s x ∂μ.measure) ∧
  (∀ (r : NNReal), 0 < r → ∀ s : ℂ,
    epsilon π χ ψ.toAddChar ((r : ENNReal) • μ.measure) a n s =
      (r : ℂ) * epsilon π χ ψ.toAddChar μ.measure a n s) ∧
  (∀ (b : F.Carrierˣ) (s : ℂ),
    epsilon π χ (ψ.toAddChar.mulShift (b : F.Carrier)) μ.measure a
        (n + T.ord (b : F.Carrier)) s =
      (χ b : ℂ) *
        Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) *
        epsilon π χ ψ.toAddChar μ.measure a n s) ∧
  (∀ ω : HarmonicAnalysis.Quasicharacter F.Carrier, conductor ω 0 →
    (∀ s : ℂ,
      epsilon π (χ * ω) ψ.toAddChar μ.measure a n s =
        (ω π : ℂ) ^ (n + (a : ℤ)) * epsilon π χ ψ.toAddChar μ.measure a n s) ∧
    (∀ t : ℂ, (ω π : ℂ) = Q t → ∀ s : ℂ,
      lFactor π (χ * ω) a s = lFactor π χ a (s + t) ∧
      epsilon π (χ * ω) ψ.toAddChar μ.measure a n s =
        epsilon π χ ψ.toAddChar μ.measure a n (s + t))) ∧
  (∀ ν : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier,
    (μ.measure O).toReal * (ν.measure O).toReal = q ^ (-n) →
    ∀ s : ℂ, epsilon π χ ψ.toAddChar μ.measure a n s *
      epsilon π χ⁻¹ ψ.toAddChar⁻¹ ν.measure a n (1 - s) = 1) ∧
  ((∀ v : F.Carrierˣ, ‖(χ v : ℂ)‖ = 1) →
    (μ.measure O).toReal = q ^ (-(n : ℝ) / 2) →
    ‖epsilon π χ ψ.toAddChar μ.measure a n (1 / 2)‖ = 1) ∧
  (∀ f : HarmonicAnalysis.SchwartzBruhat F.Carrier,
    ∃ g : HarmonicAnalysis.SchwartzBruhat F.Carrier,
      (∀ y, g y = HarmonicAnalysis.fourierTransform ψ μ f y) ∧
      ∀ Z Y : ℂ → ℂ, extendsIntegral π μ.measure f χ Z →
        extendsIntegral π μ.measure g χ⁻¹ Y →
        ∀ s₀ : ℂ,
          (fun s => Y (1 - s) / lFactor π χ⁻¹ a (1 - s))
            =ᶠ[𝓝[≠] s₀]
          (fun s => epsilon π χ ψ.toAddChar μ.measure a n s *
            (Z s / lFactor π χ a s)))

end Langlands.LocalFactor
