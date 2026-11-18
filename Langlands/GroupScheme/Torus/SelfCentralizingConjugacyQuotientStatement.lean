import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Statement: the affine quotient by a self-centralizing maximal torus's normalizer -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The affine scheme of conjugates of a self-centralizing maximal torus**
(SGA 3, Exposé XVI, Theorem 4.1(c) and the proof of 4.1(d), with Exposé XII,
Theorem 7.1(b)).

Let `G` be a smooth, separated, quasi-compact group scheme over an arbitrary
scheme `S`, whose residue-field fibres are connected and affine, and let
`t : T.toGrp ⟶ G` be a closed relative torus which is a maximal torus on every
residue-field fibre and represents its own full centralizer. Then the quotient
`G / N_G(T)` by the actual normalizer functor exists as a scheme affine over `S`:
there is a flat, surjective morphism `p : G.X ⟶ Y` locally of finite
presentation to an `S`-scheme `Y` affine over `S`, and two points of `G` on a
test scheme have the same image exactly when they differ by a point of the
normalizer. The ambient group is not assumed affine over `S`. -/
def SelfCentralizingTorusConjugacyQuotientAffineStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsSeparated G.X.hom → QuasiCompact G.X.hom →
    (∀ s : S,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
      IsFibrewiseMaximalTorus t → (torusCentralizer t).IsRepresentedBy t →
      ∃ (Y : Over S) (p : G.X ⟶ Y),
        IsAffineHom Y.hom ∧
        Flat p.left ∧ Surjective p.left ∧ LocallyOfFinitePresentation p.left ∧
        ∀ (U : Over S) (g h : U ⟶ G.X),
          g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U

end Langlands.GroupScheme
