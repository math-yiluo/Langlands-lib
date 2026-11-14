import Langlands.Representation.GodementJacquet.WhittakerModelComparisonStatement
import Langlands.AllField.Representation.GodementJacquet.Zeta
/-!
# Matrix-coefficient and Whittaker integrals on the actual coefficient model

JPSS (1983), Section (5.2), printed 420–421: once `σ` acts on its Whittaker
model, the Laurent module `I₂` of matrix-coefficient integrals equals the
Laurent module `I₃` of Whittaker integrals. This module only defines the
proposition.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding WhittakerModelComparisonStatement
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV

/-- The JPSS Section (5.2) comparison `I₂ = I₃` for the actual coefficient model.
For a representation `σ` of `GL_(n+1)` of Whittaker type for the standard
character, possibly reducible, and a nonzero standard Whittaker functional `ℓ`,
the canonical p-adic Laurent module `I₂` of the right-translation representation
on the coefficient image of `ℓ` equals the canonical p-adic Laurent module `I₃`
of the functions in that same image. No irreducibility, model admissibility,
finite generation, convergence or factor existence premise is imposed. -/
def WhittakerModelComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
    (IsOfWhittakerType n (standardCharacter ψ n) σ) →
    ∀ ℓ : (glFunctionals ψ n σ),
      ℓ.val ≠ 0 →
      Langlands.AllField.GodementJacquet.Padic.jpssI2 F (n := n) (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
          (glModelRepresentation ψ n σ ℓ) =
        Langlands.AllField.GodementJacquet.Padic.jpssI3 F ψ σ ℓ

end Langlands.AllField.GodementJacquet
