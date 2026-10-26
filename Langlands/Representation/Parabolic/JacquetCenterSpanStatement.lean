import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Parabolic.LeviBridges
import Langlands.Representation.Smooth.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite operator span for the unnormalized Jacquet block-scalar action

This is a derived prerequisite for JPS (1979), Proposition (2.2) and
Remark (2.2.5), using the actual radical quotient and product-Levi action.
The proposition is stated here; its proof is a separate unit.
-/

namespace Langlands.Parabolic

universe uF uV

/-- The actual unnormalized Jacquet action of every block-scalar tuple has
finite-dimensional complex operator span for admissible finite-type input. -/
def JacquetCenterSpanStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (m : ℕ) (B : GeneralLinear.BlockShape m),
    letI := T.topology
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear m F.Carrier) V),
      IsAdmissible ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear m F.Carrier)) ρ.asModule →
      let σ := leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range (fun a : Fin B.length → F.Carrierˣ =>
          σ (B.blockScalarLevi F.Carrier a))))

end Langlands.Parabolic
