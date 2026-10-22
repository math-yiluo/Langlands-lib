import Langlands.AbelianScheme.Isogeny
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Stability of the relative isogeny predicate -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Identity, composition, and arbitrary base-change stability for finite flat
surjective group-scheme homomorphisms. -/
def IsogenyStabilityStatement : Prop :=
  (∀ (S : Scheme.{u}) (G : Grp (Over S)), IsIsogeny (𝟙 G)) ∧
  (∀ (S : Scheme.{u}) (G H K : Grp (Over S)) (f : G ⟶ H) (g : H ⟶ K),
    IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g)) ∧
  (∀ (S T : Scheme.{u}) (b : T ⟶ S) (G H : Grp (Over S)) (f : G ⟶ H),
    IsIsogeny f → IsIsogeny ((Over.pullback b).mapGrp.map f))

end Langlands.GroupScheme
