import Langlands.Representation.Whittaker.MirabolicFiniteLengthStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Finite length of restriction to the actual mirabolic subgroup

Bernstein--Zelevinsky (1976), Corollary 5.22, printed p.51, implication (1)
implies (2), for `GL_n` over a nonarchimedean local field `F` with supplied data
`T : LocalFieldData F`. This is a proposition definition,
not a proof.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicFiniteLengthStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- A smooth complex representation of `GL_(n+1)(F)` of finite length remains
of finite length upon restriction along the actual mirabolic inclusion.
The supplied topological data determines smoothness; `n = 0` is allowed. -/
def MirabolicFiniteLengthStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F) V),
      IsSmooth ρ →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (n + 1) F)) ρ.asModule →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear.mirabolic n F))
        (Representation.asModule (ρ.comp (GeneralLinear.mirabolic n F).subtype))

end Langlands.AllField.Whittaker
