import Langlands.GroupScheme.KernelPair
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed immersions in diagrams of group extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A homomorphism of group extensions is a closed immersion if its maps on the
actual kernel and quotient are closed immersions and the source quotient map is
an fppf cover. This is an internal strengthening of Conrad's Lemma 5.3.8. -/
def FppfExtensionClosedImmersionStatement : Prop :=
  ∀ (S : Scheme.{u}) (G Q G' Q' : GroupScheme S)
    (q : G ⟶ Q) (q' : G' ⟶ Q') (f : G ⟶ G') (c : Q ⟶ Q')
    (a : kernel q ⟶ kernel q'),
    f ≫ q' = q ≫ c →
    a ≫ kernelι q' = kernelι q ≫ f →
    Flat q.hom.hom.left →
    Surjective q.hom.hom.left →
    LocallyOfFinitePresentation q.hom.hom.left →
    IsClosedImmersion a.hom.hom.left →
    IsClosedImmersion c.hom.hom.left →
    IsClosedImmersion f.hom.hom.left

end Langlands.GroupScheme
