import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement

/-!
# Upper cuspidal quotients of irreducible admissible product-Levi representations

A derived generic interface: every irreducible admissible representation of an
actual product Levi is an actual quotient of the normalized upper induction,
inside that Levi, of an irreducible cuspidal representation of a refined Levi.
This is a proposition definition, not a proof.
-/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

/-- Every irreducible admissible representation of an actual product Levi is the
target of an actual surjective intertwiner from the normalized upper refined
induction of an irreducible cuspidal representation of the flattened Levi,
transported un-twisted through the constructed flattened-Levi equivalence. -/
def LeviCuspidalQuotientStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (D : BlockShape n) (σ : Rep.{uV} ℂ (D.Levi F.Carrier)),
        Representation.IsIrreducible σ.ρ → IsAdmissible σ.ρ →
        ∃ (R : BlockRefinement D)
          (ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier)),
          Representation.IsIrreducible ω.ρ ∧
          IsLeviCuspidal (D.flatten R) ω.ρ ∧
          ∃ q : (RelativeJacquetMultiplicity.innerInduced T D R
              (RelativeJacquetMultiplicity.fineTwist T D R ω 0 0)).ρ.IntertwiningMap σ.ρ,
            Function.Surjective q

end Langlands.CuspidalSupport
