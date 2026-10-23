import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Whittaker.AsymptoticStatement
import Langlands.Representation.Whittaker.Iwasawa

/-!
# Transport of torus expansions to coefficient models

This is a conditional interface for using the canonical-topology Whittaker
expansion with the supplied topology and actual coefficient models of JPSS
integrals. It does not assert the analytic expansion without its prerequisite.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators

universe uF uV

/-- A uniform finite-function expansion for every coefficient in every model
of the representation with the specified unipotent character. -/
def CoefficientTorusExpansion {F : Type uF} [Field F] [TopologicalSpace F]
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (θ : upperUnipotent (n + 1) F →* ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) : Prop :=
  ∃ X : Finset ((Fin (n + 1) → Fˣ) → ℂ),
    (∀ χ ∈ X, Continuous χ ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : Fin (n + 1) → Fˣ => fun a => χ (b * a)))) ∧
    ∀ ℓ : functionals (upperUnipotent (n + 1) F) θ π,
    ∀ W : (coefficientModel π ℓ).toSubmodule,
      ∃ φ : ((Fin (n + 1) → Fˣ) → ℂ) → SchwartzBruhat (Fin n → F),
        ∀ a : Fin (n + 1) → Fˣ,
          W.val.val (Iwasawa.diagonalUnits a) =
            ∑ χ ∈ X, φ χ (fun i : Fin n =>
              ((a i.castSucc / a i.succ : Fˣ) : F)) * χ a

/-- The canonical full-torus statement implies the expansion needed by JPSS
coefficient models, for every supplied topology and either character sign.
The implication retains the full Whittaker-type, possibly reducible scope. -/
def ModelAsymptoticTransferStatement : Prop :=
  WhittakerTypeAsymptoticStatement.{uF, uV} →
    ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
      (T : F.TopologicalData),
      letI := T.topology
      ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (ψ : UnitaryAdditiveCharacter F.Carrier)
        (θ : upperUnipotent (n + 1) F.Carrier →* ℂˣ),
        (θ = standardCharacter ψ n ∨ θ = inverseStandardCharacter ψ n) →
        IsOfWhittakerType n θ π → CoefficientTorusExpansion θ π

end Langlands.RankinSelberg
