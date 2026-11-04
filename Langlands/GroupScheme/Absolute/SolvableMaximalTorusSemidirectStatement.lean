import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Smooth connected solvable groups as semidirect products with a maximal torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `H` be a smooth connected solvable affine group over an algebraically closed field
and let `s : T ⟶ H` be a maximal torus. Then `H` has a smooth connected normal unipotent
closed subgroup `u : U ⟶ H` containing every unipotent closed subgroup of `H`, such that
the multiplication `U × T → H`, `(n, t) ↦ n * t`, is an isomorphism of schemes. This is
Milne 2017, Theorem 16.33(d), `H = H_u ⋊ T`, with `H_u` as in Theorem 16.33(a)–(c). -/
def SolvableMaximalTorusSemidirectStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    IsSolvableGroupScheme H →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (s : T.toGrp ⟶ H),
      IsMaximalTorus s →
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ H),
        IsClosedSubgroup u ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
          (SubgroupFunctor.range u).IsNormal ∧
          (∀ (W : GroupScheme (Spec (CommRingCat.of k))) (w : W ⟶ H),
            IsClosedSubgroup w → IsUnipotent W →
              SubgroupFunctor.range w ≤ SubgroupFunctor.range u) ∧
          IsIso (subgroupMultiplication u s)

end Langlands.GroupScheme
