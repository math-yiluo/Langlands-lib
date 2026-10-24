import Langlands.Representation.RankinSelberg.ModelAsymptoticStatement
import Langlands.Representation.RankinSelberg.RootTorusProductStatement

/-! Uniform root-coordinate expansions for the actual coefficient models. -/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker
open scoped BigOperators

universe uF uV uW

/-- Assumed coefficient torus expansions give one finite-function family for
all functionals, coefficients, row tests and right translates. -/
def EqualRankRootExpansionStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  let A := Fin (n + 1) → F.Carrierˣ
  let toDiagonal : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let weight : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ψ : UnitaryAdditiveCharacter F.Carrier),
    CoefficientTorusExpansion (standardCharacter ψ n) π →
    CoefficientTorusExpansion (inverseStandardCharacter ψ n) σ →
  ∃ (m : ℕ) (η : Fin m → A → ℂ),
    (∀ j, Continuous (η j) ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : A => fun a : A => η j (b * a)))) ∧
    ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
      (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (k : Langlands.GeneralLinear (n + 1) F.Carrier),
    ∃ Ψ : Fin m → SchwartzBruhat (Fin (n + 1) → F.Carrier),
      ∀ a : A,
        let g := GeneralLinear.Iwasawa.diagonalUnits (toDiagonal a) * k
        f.val.val g * f'.val.val g * Φ (lastRow g) * weight a =
          ∑ j, Ψ j (fun i => (a i : F.Carrier)) * η j a

end Langlands.RankinSelberg
