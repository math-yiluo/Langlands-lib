import Langlands.GroupScheme.Reductive.Basic

/-! # Normal closed subgroups as kernels of finite-dimensional representations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MatrixRepresentation

/-- Every normal closed subgroup of an affine finite-type group scheme over a
field is the scheme-theoretic kernel of a finite-dimensional representation. -/
def NormalKernelStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
        ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          SubgroupFunctor.range (kernelι ρ) = SubgroupFunctor.range i

end Langlands.GroupScheme.MatrixRepresentation
