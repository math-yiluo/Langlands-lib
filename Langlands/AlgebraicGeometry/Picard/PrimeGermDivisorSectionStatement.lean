import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Line-bundle sections cutting out the prime divisor of a prime germ

On an integral locally Noetherian scheme whose stalks are unique factorization domains,
a prime element `π` of the stalk at a point `e` determines a prime divisor through `e`.
This module states that this divisor is the zero locus of a global section of an actual
line bundle, with local equation `π` at `e`. This module supplies a statement target, not
a proof.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule

/-- Let `X` be an integral locally Noetherian scheme all of whose stalks are unique
factorization monoids, `e` a point and `π` a prime element of the stalk at `e`. Then some
line bundle `L` on `X` has a global section `s` such that:
* `e` is not in the generation open of `s`;
* the generation open of `s` is nonempty;
* for every function `f` on an open `U ∋ e` whose germ at `e` is divisible by `π`, the
  basic open of `f` lies in the generation open of `s`;
* there are an open `V ∋ e` and a function `a` on `V` whose germ at `e` is associated to
  `π`, such that `s` vanishes along any morphism `g` landing in `V` exactly when the
  pullback of `a` along `g` is zero.
This proposition is a statement target, not a proof. -/
def PrimeGermDivisorSectionStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) →
    ∀ (e : X) (π : X.presheaf.stalk e), Prime π →
      ∃ (L : LineBundle X) (s : GlobalSections L.obj),
        e ∉ trivializationOpen L.obj s ∧
        (trivializationOpen L.obj s : Set X).Nonempty ∧
        (∀ (U : X.Opens) (heU : e ∈ U) (f : Γ(X, U)),
          π ∣ X.presheaf.germ U e heU f → X.basicOpen f ≤ trivializationOpen L.obj s) ∧
        ∃ (V : X.Opens) (heV : e ∈ V) (a : Γ(X, V)),
          Associated (X.presheaf.germ V e heV a) π ∧
          ∀ (T : Scheme.{u}) (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ V),
            VanishesAlong L g s ↔ g.appLE V ⊤ hg a = 0

end Langlands.AlgebraicGeometry.Picard
