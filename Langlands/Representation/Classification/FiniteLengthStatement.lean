import Langlands.LocalField.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.FiniteLength
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-!
# Finite length of finitely generated admissible representations of GL_n

This is the GL_n specialization of Silberger (1979), Theorem 5.4.1.6,
pp.291-292. It is a proposition definition, not a proof.
-/

namespace Langlands

universe uF uV

/-- An admissible complex representation of GL_n over a finite extension of
Q_p has finite length if it is finitely generated as a group module.
The field has its canonical finite-dimensional module topology. -/
def GLAdmissibleFiniteLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopology
    ∀ (n : ℕ), 0 < n →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) F.Carrier) V),
        IsAdmissible ρ →
        Module.Finite (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) F.Carrier))
          ρ.asModule →
        IsFiniteLength (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) F.Carrier))
          ρ.asModule

end Langlands
