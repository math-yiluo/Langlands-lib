import Langlands.Representation.Parabolic.JacquetCenterSpanStatement
import Langlands.AllField.Group.GL.BlockIwahoriDefinitions
/-!
# Finite operator span for the unnormalized Jacquet block-scalar action

This is a derived prerequisite for JPS (1979), Proposition (2.2) and
Remark (2.2.5), using the actual radical quotient and product-Levi action.
The proposition is stated here; its proof is a separate unit.
-/

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding JacquetCenterSpanStatement
open Langlands.AllField.Parabolic

universe uF uV

/-- The actual unnormalized Jacquet action of every block-scalar tuple has
finite-dimensional complex operator span for admissible finite-type input. -/
def JacquetCenterSpanStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (m : ℕ) (B : GeneralLinear.BlockShape m),
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear m F) V),
      IsAdmissible ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear m F)) ρ.asModule →
      let σ := leviCoinvariants B (ρ.comp (B.parabolic F).subtype)
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range (fun a : Fin B.length → Fˣ =>
          σ (B.blockScalarLevi F a))))

end Langlands.AllField.Parabolic
