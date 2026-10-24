import Langlands.LocalField.Definitions
import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Whittaker.GeneralLinear
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Whittaker multiplicity at most one

The scalar form of the dimension-zero-or-one assertion recalled in JPSS
(1983), Section 2.1, page 385. This module defines an unproved proposition.
-/

namespace Langlands.Whittaker

universe uF uV

/-- Every nonzero standard Whittaker functional on an irreducible admissible
complex representation of a positive-rank p-adic general linear group spans
the functional space, with a unique scalar for each functional. -/
def MultiplicityOneStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      IsAdmissible π → Representation.IsIrreducible π →
      ∀ ℓ₁ ℓ₂ : glFunctionals ψ n π, ℓ₁.val ≠ 0 →
        ∃! c : ℂ, ℓ₂ = c • ℓ₁

end Langlands.Whittaker
