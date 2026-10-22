import Langlands.LocalFactor.RegularEvaluation.Adapters

/-! Comparison targets for the published adapters; proofs are a separate contribution. -/

namespace Langlands.LocalFactor.RegularEvaluation

universe uK uV uW uF

/-- The polynomial Euler adapter preserves its full regular domain, input, and unit value. -/
def EulerComparison {K : Type uK} [Field K]
    {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Module.End K V) : Prop :=
  (∀ z : K, (∃ x : LocalFactor.RegularPoint A, x.val = z) ↔
    (eulerPolynomial A).eval z ≠ 0) ∧
  (∀ x : LocalFactor.RegularPoint A,
    (regularEvaluationEquiv A x).val = x.val) ∧
  (∀ x : Point (eulerPolynomial A).eval,
    ((regularEvaluationEquiv A).symm x).val = x.val) ∧
  (∀ x : LocalFactor.RegularPoint A,
    regularFactorValue A x = value (eulerPolynomial A).eval (regularEvaluationEquiv A x))

/-- The spectral Euler adapter preserves the spectral input; its polynomial map
uses the actual spectral substitution and preserves reciprocal evaluation. -/
def SpectralEulerComparison {V : Type uW} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q) : Prop :=
  (∀ s : ℂ, (∃ x : SpectralRegularPoint A q hq, x.val = s) ↔
    (eulerPolynomial A).eval (spectralParameter q hq s : ℂ) ≠ 0) ∧
  (∀ x : SpectralRegularPoint A q hq,
    (spectralRegularEvaluationEquiv A q hq x).val = x.val) ∧
  (∀ x : Point ((eulerPolynomial A).eval ∘ fun s => (spectralParameter q hq s : ℂ)),
    ((spectralRegularEvaluationEquiv A q hq).symm x).val = x.val) ∧
  (∀ x : SpectralRegularPoint A q hq,
    spectralFactorValue A q hq x =
      value ((eulerPolynomial A).eval ∘ fun s => (spectralParameter q hq s : ℂ))
        (spectralRegularEvaluationEquiv A q hq x)) ∧
  (∀ x : SpectralRegularPoint A q hq,
    (spectralToPolynomialPoint A q hq x).val = (spectralParameter q hq x.val : ℂ)) ∧
  (∀ x : SpectralRegularPoint A q hq,
    value (eulerPolynomial A).eval (spectralToPolynomialPoint A q hq x) =
      value ((eulerPolynomial A).eval ∘ fun s => (spectralParameter q hq s : ℂ))
        (spectralRegularEvaluationEquiv A q hq x)) ∧
  (∀ x : SpectralRegularPoint A q hq,
    spectralFactorValue A q hq x =
      value (eulerPolynomial A).eval (spectralToPolynomialPoint A q hq x))

/-- Only regular numerical evaluation is compared; the original entire object,
its punctured germs, and its pole predicate are retained. -/
def ReciprocalEntireComparison (F : ReciprocalEntire) : Prop :=
  (∀ z : ℂ, (∃ x : F.RegularPoint, x.val = z) ↔ F.denominator z ≠ 0) ∧
  (∀ x : F.RegularPoint, (F.regularEvaluationEquiv x).val = x.val) ∧
  (∀ x : Point F.denominator, (F.regularEvaluationEquiv.symm x).val = x.val) ∧
  (∀ x : F.RegularPoint, F.eval x = value F.denominator (F.regularEvaluationEquiv x))

/-- The p-adic comparison uses precisely the actual conductor and uniformizer.
The original arbitrary-conductor predicate is neither replaced nor generalized. -/
def PadicAbelianComparison {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology) : Prop :=
  (∀ s : ℂ,
    PadicAbelian.RegularPoint T (PadicAbelian.uniformizerUnit T) χ
        (T.multiplicativeConductor χ) s ↔
      (PadicAbelian.lPolynomial T χ).eval (PadicAbelian.spectralVariable T s) ≠ 0) ∧
  (∀ x : {s : ℂ // PadicAbelian.RegularPoint T (PadicAbelian.uniformizerUnit T) χ
      (T.multiplicativeConductor χ) s},
    (PadicAbelian.regularEvaluationEquiv T χ x).val = x.val) ∧
  (∀ x : Point ((PadicAbelian.lPolynomial T χ).eval ∘ PadicAbelian.spectralVariable T),
    ((PadicAbelian.regularEvaluationEquiv T χ).symm x).val = x.val) ∧
  (∀ x : {s : ℂ // PadicAbelian.RegularPoint T (PadicAbelian.uniformizerUnit T) χ
      (T.multiplicativeConductor χ) s},
    PadicAbelian.regularLValue T χ x =
      value ((PadicAbelian.lPolynomial T χ).eval ∘ PadicAbelian.spectralVariable T)
        (PadicAbelian.regularEvaluationEquiv T χ x)) ∧
  (∀ x : {s : ℂ // PadicAbelian.RegularPoint T (PadicAbelian.uniformizerUnit T) χ
      (T.multiplicativeConductor χ) s},
    (PadicAbelian.regularToPolynomialPoint T χ x).val = PadicAbelian.spectralVariable T x.val) ∧
  (∀ x : {s : ℂ // PadicAbelian.RegularPoint T (PadicAbelian.uniformizerUnit T) χ
      (T.multiplicativeConductor χ) s},
    value (PadicAbelian.lPolynomial T χ).eval (PadicAbelian.regularToPolynomialPoint T χ x) =
      value ((PadicAbelian.lPolynomial T χ).eval ∘ PadicAbelian.spectralVariable T)
        (PadicAbelian.regularEvaluationEquiv T χ x)) ∧
  (∀ x : {s : ℂ // PadicAbelian.RegularPoint T (PadicAbelian.uniformizerUnit T) χ
      (T.multiplicativeConductor χ) s},
    PadicAbelian.regularLValue T χ x =
      value (PadicAbelian.lPolynomial T χ).eval (PadicAbelian.regularToPolynomialPoint T χ x))

/-- Exact target combining the four comparisons, with independent carrier universes. -/
def ComparisonStatement : Prop :=
  (∀ (K : Type uK) [Field K] (V : Type uV) [AddCommGroup V]
      [Module K V] [FiniteDimensional K V] (A : Module.End K V),
    EulerComparison A) ∧
  (∀ (V : Type uW) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q),
    SpectralEulerComparison A q hq) ∧
  (∀ F : ReciprocalEntire, ReciprocalEntireComparison F) ∧
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology),
    PadicAbelianComparison T χ)

end Langlands.LocalFactor.RegularEvaluation
