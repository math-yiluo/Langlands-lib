import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: torus envelope normality over a finite field when all cocharacters are central -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over a finite field, if every cocharacter of a smooth connected affine group is central
(its dynamic centralizer is the whole group on every test scheme), then the closed envelope of
all ground-field tori is normal on every test scheme. -/
def FiniteFieldCentralCocharacterEnvelopeNormalityStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, Dynamic.centralizer χ = ⊤) →
      (closedTorusEnvelope G).IsNormal

end Langlands.GroupScheme
