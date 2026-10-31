import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Smooth.Definitions

/-!
# Admissibility of actual normalized upper refined Jacquet modules

The upper counterpart of
`Langlands.Parabolic.RefinedOppositeJacquetAdmissibilityStatement`.
This module states a proposition and supplies no proof.
-/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- The actual normalized upper Jacquet module, along an inner block
refinement, of an admissible representation of an outer product Levi is
admissible. -/
def UpperRefinedJacquetAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V),
      IsAdmissible ρ →
        IsAdmissible (T.normalizedRefinedJacquet B S ρ)

end Langlands.Parabolic
