import Langlands.AbelianScheme.KernelCharacterIndependence
import Langlands.AbelianScheme.IsogenySpecialization

/-! # Injectivity of the normalized character of trivial isogeny pullbacks -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over every base and on every test scheme, two actual line bundles with
trivial isogeny pullback and the same normalized kernel character are
isomorphic. -/
def TrivialPullbackCharacterInjectiveStatement : Prop :=
  ∀ (S : Scheme.{u}) (A B : AbelianScheme S) (f : A ⟶ B), IsIsogeny f →
    ∀ (T : Over S),
      Function.Injective
        (trivialHomPullbackClassCharacter f (T := T) (universalGlobalFunctions A))

end Langlands.AbelianScheme
