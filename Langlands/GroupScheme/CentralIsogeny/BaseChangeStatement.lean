import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.AbelianScheme.IsogenyStability
import Langlands.AbelianScheme.KernelBaseChange

/-! # Arbitrary base change of central isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Central isogenies remain central isogenies after every morphism of base schemes,
with the full scheme-theoretic kernel over the new base. -/
def CentralIsogenyBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (G H : GroupScheme S) (f : G ⟶ H),
    IsCentralIsogeny f → IsCentralIsogeny ((GroupScheme.baseChange b).map f)

end Langlands.GroupScheme
