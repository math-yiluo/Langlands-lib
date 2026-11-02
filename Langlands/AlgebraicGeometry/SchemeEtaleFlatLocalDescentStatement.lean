import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Pointwise etale descent in a flat scheme pullback -/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- In a pullback of a locally finitely presented morphism along a flat
morphism, flatness and formal unramifiedness at a point of the pullback
imply formal etaleness at its image in the original source. -/
def SchemeEtaleFlatLocalDescentStatement : Prop :=
  ∀ (X S T P : Scheme.{u}) (f : X ⟶ S) (g : T ⟶ S)
    (a : P ⟶ X) (p : P ⟶ T),
    IsPullback a p f g → Flat g → LocallyOfFinitePresentation f →
      ∀ z : P, (p.stalkMap z).hom.Flat →
        (p.stalkMap z).hom.FormallyUnramified →
          (f.stalkMap (a z)).hom.FormallyEtale

end Langlands.AlgebraicGeometry
