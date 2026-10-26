import Langlands.Representation.Whittaker.KirillovStatement
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Kirillov lifting into actual coefficient models

An internal conditional interface for the compact mirabolic model of JPSS
(1983), Section 2.2, printed page 386. These proposition definitions do not
prove Kirillov surjectivity.
-/

namespace Langlands.Whittaker

open HarmonicAnalysis GeneralLinear RankinSelberg

universe uF uV

/-- The smoothness and compact-support conditions on the mirabolic restriction.
The ambient `WhittakerFunctions` subtype already supplies unipotent covariance.
No smoothness or compact support away from the mirabolic subgroup is required. -/
def IsMirabolicTestFunction {F : Type uF} [Field F] [TopologicalSpace F]
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (φ : WhittakerFunctions ψ n) : Prop :=
  (∃ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
    ∀ q k : Langlands.GeneralLinear (n + 1) F,
      (∀ a, q.val (Fin.last n) a = if a = Fin.last n then 1 else 0) →
      (∀ a, k.val (Fin.last n) a = if a = Fin.last n then 1 else 0) →
      k ∈ K → φ.val (q * k) = φ.val q) ∧
  (∃ C : Set (Langlands.GeneralLinear (n + 1) F), IsCompact C ∧
    ∀ q : Langlands.GeneralLinear (n + 1) F,
      (∀ a, q.val (Fin.last n) a = if a = Fin.last n then 1 else 0) →
      φ.val q ≠ 0 →
      ∃ (u : upperUnipotent (n + 1) F) (c : Langlands.GeneralLinear (n + 1) F),
        c ∈ C ∧ q = u.val * c)

/-- The assumed full canonical Kirillov proposition implies lifting of every
mirabolic test function into each nonzero-functional coefficient model, for
every supplied topology and every representation of Whittaker type. -/
def ModelKirillovTransferStatement : Prop :=
  Langlands.WhittakerTypeKirillovStatement.{uF, uV} →
    ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
      (T : F.TopologicalData),
      letI := T.topology
      ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (ψ : UnitaryAdditiveCharacter F.Carrier),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        ∀ ℓ : glFunctionals ψ n π, ℓ.val ≠ 0 →
        ∀ φ : WhittakerFunctions ψ n, IsMirabolicTestFunction ψ n φ →
          ∃ f : (coefficientModel π ℓ).toSubmodule,
            ∀ q : Langlands.GeneralLinear (n + 1) F.Carrier,
              (∀ a, q.val (Fin.last n) a = if a = Fin.last n then 1 else 0) →
              f.val.val q = φ.val q

end Langlands.Whittaker
