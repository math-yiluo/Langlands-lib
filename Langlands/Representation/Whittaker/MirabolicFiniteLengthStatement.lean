import Langlands.Group.GL.Mirabolic
import Langlands.LocalField.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.FiniteLength

/-!
# Finite length of restriction to the actual mirabolic subgroup

The p-adic specialization of Bernstein--Zelevinsky (1976), Corollary 5.22,
printed p.51, implication (1) implies (2). This is a proposition definition,
not a proof.
-/

namespace Langlands.Whittaker

universe uF uV

/-- A smooth complex representation of `GL_(n+1)(F)` of finite length remains
of finite length upon restriction along the actual mirabolic inclusion.
The supplied topological data determines smoothness; `n = 0` is allowed. -/
def MirabolicFiniteLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V),
      IsSmooth ρ →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)) ρ.asModule →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F.Carrier))
        (Representation.asModule (ρ.comp (GeneralLinear.mirabolic n F.Carrier).subtype))

end Langlands.Whittaker
