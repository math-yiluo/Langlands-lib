import Langlands.Representation.GodementJacquet.ModelWhittakerRationalityStatement
import Langlands.AllField.Representation.GodementJacquet.Zeta
/-!
# Convergence and rationality of each Whittaker matrix integral on the model

JPSS (1983), Section (5.2), printed 420–421: for `σ` of Whittaker type acting on
its Whittaker model, every full-matrix integral
`Z(Φ, s, W) = ∫ Φ(g) W(g) |det g|^s dg` converges for `Re s` large and defines a
rational function of `q^(-s)`. The common g.c.d. asserted there is not part of
this proposition. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV

/-- Every shifted full-matrix Whittaker integral on the actual coefficient model
converges on some right half-plane and has a rational continuation in
`q^(-s)`. For a representation `σ` of `GL_(n+1)` of Whittaker type for the
standard character, possibly reducible, a nonzero standard Whittaker functional
`ℓ`, any Schwartz–Bruhat function `Φ` on all square matrices and any function
`W` of the coefficient image of `ℓ`, the integral
`∫ Φ(g) W(g) |det g|^(s + n/2) dg` for the normalized Haar measure converges
absolutely for `Re s > a` for some real `a`, and agrees there with a rational
function of `q^(-s)`. Each half-plane may depend on `Φ` and `W`. -/
def ModelWhittakerRationalityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
    (IsOfWhittakerType n (standardCharacter ψ n) σ) →
    ∀ ℓ : (glFunctionals ψ n σ),
      ℓ.val ≠ 0 →
      ∀ (Φ : MatrixTestFunction n F) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule),
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n) (glModelFunction ψ n σ ℓ w)) ∧
        ∃ R : RationalFunctions,
          HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
            (fun s => Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift n)
              (glModelFunction ψ n σ ℓ w)) R

end Langlands.AllField.GodementJacquet
