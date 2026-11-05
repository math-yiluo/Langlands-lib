import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Positive powers of rational points: a torus and an additive factor -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A positive power of a rational point of a smooth affine group over any field
is the product of a rational point of a closed torus and the value at additive
coordinate `1` of an actual morphism from the additive group scheme. -/
def PositivePowerTorusAdditiveFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (x : rationalPoints G),
    ∃ (m : ℕ), 0 < m ∧
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
        (t : rationalPoints T.toGrp)
        (φ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G),
        IsTorus T.toGrp ∧ IsClosedSubgroup i ∧
          x ^ m = rationalPoints.map i t *
            rationalPoints.map φ
              ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
                (Multiplicative.ofAdd (fun _ => 1)))

end Langlands.GroupScheme
