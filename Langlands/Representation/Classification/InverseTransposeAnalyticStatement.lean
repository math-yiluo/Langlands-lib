import Langlands.Representation.Classification.Tempered
import Langlands.Group.GL.Maps

/-!
# Analytic inverse-transpose transport

Proposition definitions for preservation and reflection of analytic temperedness
and square-integrability under the actual inverse-transpose automorphism of
p-adic `GL_n`. The predicates and their quantification over all Borel Haar
measures on the central quotient are unchanged. No transport theorem is proved
or assumed here.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Inverse-transpose pullback preserves and reflects analytic temperedness in
every positive rank, with the representation carrier independent of the field. -/
def InverseTransposeTemperedClause : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      T.IsTempered (ρ.comp (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom) ↔
        T.IsTempered ρ

/-- Inverse-transpose pullback preserves and reflects analytic
square-integrability modulo the center in every positive rank. -/
def InverseTransposeSquareIntegrableClause : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      T.IsSquareIntegrable
          (ρ.comp (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom) ↔
        T.IsSquareIntegrable ρ

/-- Both analytic transport clauses for every prime, p-adic field and compatible
topological realization. This is a statement target, not a proof. -/
def PadicInverseTransposeAnalyticStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    InverseTransposeTemperedClause.{uF, uV} T ∧
      InverseTransposeSquareIntegrableClause.{uF, uV} T

end Langlands.Classification
