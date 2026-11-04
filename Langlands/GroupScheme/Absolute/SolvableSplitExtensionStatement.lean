import Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement

/-! # Splitting of the torus quotient of a solvable group over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `H` be a smooth connected solvable affine group over an algebraically closed field,
let `i : U ⟶ H` be a smooth connected unipotent closed subgroup with normal range, and let
`q : H ⟶ D` be a represented fppf quotient by that range onto a split torus `D`. Then `q`
has a homomorphic section `σ : D ⟶ H`, so the extension `e → U → H → D → e` splits. This is
Milne 2017, Theorem 16.26(a), for the trigonalizable group `H`. This declaration is a
proposition target. -/
def SolvableSplitExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    IsSolvableGroupScheme H →
    ∀ (U D : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ H) (q : H ⟶ D),
      IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
        (SubgroupFunctor.range i).IsNormal →
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q → IsSplitTorus D →
        ∃ σ : D ⟶ H, σ ≫ q = 𝟙 D

end Langlands.GroupScheme
