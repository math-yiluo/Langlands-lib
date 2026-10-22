import Langlands.AbelianScheme.Isogeny
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Fibrewise detection of isogenies between smooth proper group schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A homomorphism between smooth proper group schemes is finite, flat, and
surjective if its pullback over every residue-field point of the base is so.
This proposition is a statement target, not a proof of the criterion. -/
def FiberwiseIsogenyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : Grp (Over S)),
    Smooth G.X.hom → Smooth H.X.hom →
      IsProper G.X.hom → IsProper H.X.hom →
        ∀ (f : G ⟶ H),
          (∀ s : S, IsIsogeny ((Over.pullback (S.fromSpecResidueField s)).mapGrp.map f)) →
            IsIsogeny f

end Langlands.GroupScheme
