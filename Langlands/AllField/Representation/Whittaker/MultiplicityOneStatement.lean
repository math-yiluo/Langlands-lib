import Langlands.Representation.Whittaker.MultiplicityOneStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Whittaker multiplicity at most one

The scalar form of the dimension-zero-or-one assertion recalled in JPSS
(1983), Section 2.1, page 385. This module defines an unproved proposition.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MultiplicityOneStatement
open Langlands.AllField.Whittaker

universe uF uV

/-- Every nonzero standard Whittaker functional on an irreducible admissible
complex representation of a positive-rank general linear group over a
nonarchimedean local field, with the topology of the supplied data `T`, spans
the functional space, with a unique scalar for each functional. -/
def MultiplicityOneStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
      IsAdmissible π → Representation.IsIrreducible π →
      ∀ ℓ₁ ℓ₂ : glFunctionals ψ n π, ℓ₁.val ≠ 0 →
        ∃! c : ℂ, ℓ₂ = c • ℓ₁

end Langlands.AllField.Whittaker
