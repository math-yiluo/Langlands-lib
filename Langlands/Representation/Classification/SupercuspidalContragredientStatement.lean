import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Supercuspidality and the smooth contragredient: proposition target

This module states, and does not prove, that the smooth contragredient
preserves and reflects the actual supercuspidal condition, and the
irreducibility of admissible representations, of `GL_n(F)` for every p-adic
field `F`.
-/

namespace Langlands.GeneralLinear

universe uF uV

/-- For every p-adic field, field realization, rank and smooth complex
representation `ρ` of `GL_n(F)`: the smooth contragredient of `ρ` is
supercuspidal exactly when `ρ` is, and for admissible `ρ` it is irreducible
exactly when `ρ` is. -/
def SupercuspidalContragredientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsSmooth ρ →
        (IsSupercuspidal (smoothContragredient ρ) ↔ IsSupercuspidal ρ) ∧
        (IsAdmissible ρ →
          (Representation.IsIrreducible (smoothContragredient ρ) ↔
            Representation.IsIrreducible ρ))

end Langlands.GeneralLinear
