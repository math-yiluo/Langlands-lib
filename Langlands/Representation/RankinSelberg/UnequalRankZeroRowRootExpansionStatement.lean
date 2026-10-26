import Langlands.Representation.RankinSelberg.ModelAsymptoticStatement
import Langlands.Representation.RankinSelberg.QuotientRootIntegrationStatement

/-!
# Uniform root expansions of zero-row unequal-rank coefficients

This internal conditional statement isolates the pointwise root expansion
behind the diagonal restriction in JPSS, printed page 394, display (7).
The two full-torus expansion premises supply the finite-function families.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators

universe uF uV uW

/-- A fixed finite family of continuous translation-finite functions expands
all actual zero-row coefficient products at compact right translates.
The determinant shift is included in that family, before the spectral parameter
is chosen. No analytic convergence or extra representation hypothesis is used. -/
def UnequalRankZeroRowRootExpansionStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let A := Fin (n + 1) → F.Carrierˣ
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ
      (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ψ : UnitaryAdditiveCharacter F.Carrier),
    CoefficientTorusExpansion (standardCharacter ψ (n + (0 + k + 1))) π →
    CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
    ∃ (m : ℕ) (η : Fin m → A → ℂ),
      (∀ i, Continuous (η i) ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : A => fun a : A => η i (b * a)))) ∧
      ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
        (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (z : K),
        ∃ Ψ : Fin m → SchwartzBruhat (Fin (n + 1) → F.Carrier),
          ∀ (a : A) (s : ℂ),
            unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
                (Iwasawa.diagonalUnits (d a) * z.val) * w a =
              ∑ i, Ψ i (fun j => (a j : F.Carrier)) * η i a *
                ∏ j, (T.normalizedAbs (a j : F.Carrier) : ℂ) ^
                  ((j.val + 1 : ℂ) * s)

end Langlands.RankinSelberg
