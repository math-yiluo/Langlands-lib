import Langlands.Representation.Whittaker.IrreducibleCoinvariantFinitenessStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Finite twisted upper-unipotent coinvariants of irreducible representations

The finiteness assertion of Bernstein--Zelevinsky (1976), Theorem 5.21, printed
p.51, for `GL_n` over a nonarchimedean local field `F` with supplied data
`T : LocalFieldData F`. This is a proposition definition, not a
proof.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding IrreducibleCoinvariantFinitenessStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- For an irreducible smooth complex representation of the actual `GL_n(F)`
and every locally constant character of the actual upper-unipotent subgroup,
the actual character-localized coinvariant quotient is finite-dimensional.
The supplied topological data determines smoothness and local constancy;
`n = 0` is allowed. -/
def IrreducibleCoinvariantFinitenessStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F) V),
      IsSmooth ρ → ρ.IsIrreducible →
      ∀ θ : GeneralLinear.upperUnipotent n F →* ℂˣ,
        IsLocallyConstant (fun u => (θ u : ℂ)) →
        FiniteDimensional ℂ
          (Jacquet.Localization.Coinvariants ρ
            (GeneralLinear.upperUnipotent n F) θ)

end Langlands.AllField.Whittaker
