import Langlands.AlgebraicGeometry.Modules.FibreNeighbourhoodSections
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingStatement

/-! # Eventual lifting of fibre sections of a specified ample power -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

/-- For a proper family over a locally noetherian base, if a specified
line bundle is ample on a residue-field fibre, then every section of
every sufficiently high power on that fibre comes from a section over
the inverse image of an affine neighbourhood of the base point.
This is a proposition target, not a proof. -/
def ProperFibrePowerSectionLiftingStatement : Prop :=
  ∀ (X S : Scheme.{u}) [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : LineBundle X) (s : S),
    ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∀ σ : GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj
          (tensorPow L.obj n)),
          ∃ (V : S.Opens) (hsV : s ∈ V), IsAffineOpen V ∧
            ∃ τ : Γ(tensorPow L.obj n, f ⁻¹ᵁ V),
              fibreNeighbourhoodSection f s (tensorPow L.obj n) hsV τ = σ

end Langlands.AlgebraicGeometry.Modules
