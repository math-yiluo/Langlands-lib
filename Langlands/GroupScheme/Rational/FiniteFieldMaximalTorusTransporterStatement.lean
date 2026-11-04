import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Statement: conjugates of a maximal torus over a finite field lie in the torus envelope -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over a finite field, a smooth connected affine group has a maximal torus all of whose
conjugates, by points of the group on every test scheme, lie in the closed envelope of all
ground-field tori. -/
def FiniteFieldMaximalTorusTransporterStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
      IsMaximalTorus j₀ ∧
        ∀ (U : Over (Spec (CommRingCat.of k))) (g x : U ⟶ G.X),
          x ∈ (SubgroupFunctor.range j₀).carrier U →
            g * x * g⁻¹ ∈ (closedTorusEnvelope G).carrier U

end Langlands.GroupScheme
