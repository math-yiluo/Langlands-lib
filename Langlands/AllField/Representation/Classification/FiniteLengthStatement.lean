import Langlands.Representation.Classification.FiniteLengthStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Finite length of finitely generated admissible representations of GL_n

This is the GL_n specialization of Silberger (1979), Theorem 5.4.1.6,
pp.291-292. It is a proposition definition, not a proof.
-/

namespace Langlands.AllField

universe uF uV

/-- An admissible complex representation of GL_n over a nonarchimedean local
field has finite length if it is finitely generated as a group module.
The field carries the topology of the supplied data `T : LocalFieldData F`. -/
def GLAdmissibleFiniteLengthStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) F) V),
        IsAdmissible ρ →
        Module.Finite (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) F))
          ρ.asModule →
        IsFiniteLength (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) F))
          ρ.asModule

end Langlands.AllField
