import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicInnerTypeAStatement
import Langlands.GroupScheme.Examples.HermitianMatrixPresentation

/-!
# Outer forms of type A are special unitary groups when unitary algebras split

This module states that, over a field `K` over which every central simple algebra
with a unitary involution (relative to a separable quadratic extension) is split,
every simply connected absolutely almost-simple group whose actual index has type
`A_n` and whose actual star action is nontrivial has an all-test presentation as the
special unitary group of a nonsingular Hermitian matrix of size `n + 1` over a
separable quadratic extension of `K`. It supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- If `K` has the splitting property `UnitaryInvolutionSplitting K`, then every
affine, locally finite-type, simply connected, absolutely almost-simple group `G`
over `K` whose actual index `d` has type `A_n` and whose actual star action moves
some simple vertex admits a separable quadratic extension `L/K`, a nonsingular
Hermitian form `J` on `L^(n+1)` for the nontrivial automorphism of `L/K`, and an
all-test presentation `HermitianMatrix.SchemeModel.Presentation K L J G` of `G` as
the determinant-one isometry group of `J`. -/
def OuterTypeAUnitarySplitPresentationStatement : Prop :=
  ∀ (K : Type u) [Field K], UnitaryInvolutionSplitting K →
    ∀ (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
      IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
      (∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
        d.star σ a ≠ a) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsQuadraticExtension K L) (_ : Algebra.IsSeparable K L)
        (J : HermitianMatrix.Form (SU3Root.fieldInvolution K L) (Fin (n + 1))),
        Nonempty (HermitianMatrix.SchemeModel.Presentation K L J G)

end Langlands.GroupScheme
