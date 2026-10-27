import Langlands.Group.GL.UpperUnipotent
import Langlands.LocalField.Definitions
import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Jacquet.Localization
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Finite twisted upper-unipotent coinvariants of irreducible representations

The p-adic specialization of the finiteness assertion of Bernstein--Zelevinsky
(1976), Theorem 5.21, printed p.51. This is a proposition definition, not a
proof.
-/

namespace Langlands.Whittaker

universe uF uV

/-- For an irreducible smooth complex representation of the actual `GL_n(F)`
and every locally constant character of the actual upper-unipotent subgroup,
the actual character-localized coinvariant quotient is finite-dimensional.
The supplied topological data determines smoothness and local constancy;
`n = 0` is allowed. -/
def IrreducibleCoinvariantFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsSmooth ρ → ρ.IsIrreducible →
      ∀ θ : GeneralLinear.upperUnipotent n F.Carrier →* ℂˣ,
        IsLocallyConstant (fun u => (θ u : ℂ)) →
        FiniteDimensional ℂ
          (Jacquet.Localization.Coinvariants ρ
            (GeneralLinear.upperUnipotent n F.Carrier) θ)

end Langlands.Whittaker
