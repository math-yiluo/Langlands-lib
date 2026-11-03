import Langlands.GroupScheme.Rational.Characters
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Maximality of a supplied split-torus image under a central surjection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, a supplied fppf image of a maximal split torus under an actual
central fppf surjection of connected reductive group schemes is maximal split.
Centrality refers to the actual scheme-theoretic kernel; no smoothness or finiteness
assumption is imposed on that kernel. -/
def CentralSurjectionMaximalSplitTorusImageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ H),
    IsConnectedReductive G → IsConnectedReductive H →
    Flat q.hom.hom.left → Surjective q.hom.hom.left →
    LocallyOfFinitePresentation q.hom.hom.left → IsCentral (kernelι q) →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ H) (p : T ⟶ T'),
      IsMaximalSplitTorus i → IsSplitSubtorus j →
      Flat (CommGroupScheme.groupHom p).hom.hom.left →
      Surjective (CommGroupScheme.groupHom p).hom.hom.left →
      LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left →
      CommGroupScheme.groupHom p ≫ j = i ≫ q → IsMaximalSplitTorus j

end Langlands.GroupScheme
