import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Jacquet.Localization
import Langlands.Group.GL.Mirabolic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Absence of degenerate mirabolic submodules over local fields

Theorem 4.9 of Bernstein and Zelevinsky (1977), expressed using the full
upper-unipotent character quotient instead of normalized iterated derivatives.
-/

namespace Langlands.Whittaker

open Langlands.GeneralLinear Langlands.HarmonicAnalysis

universe uF uV

/-- An irreducible admissible generic representation of `GL_(n+1)(F)` has no
nonzero mirabolic subrepresentation whose standard full upper-unipotent
character quotient vanishes. The field may have any characteristic. -/
def LocalFieldMirabolicNondegeneracyStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
    IsGeneric ψ n π →
    ∀ U : Subrepresentation (π.comp (mirabolic n F).subtype),
      Subsingleton
        (Jacquet.Localization.Coinvariants U.toRepresentation
          (Mirabolic.upperUnipotent n F)
          ((standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom)) →
      U = ⊥

end Langlands.Whittaker
