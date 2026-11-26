import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicInnerTypeAStatement
import Langlands.GroupScheme.Examples.UnitaryAlgebraPresentation
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic

/-!
# Outer forms of type A are special unitary groups of algebras with involution

This module states that over every field `K`, every simply connected absolutely almost-simple
group whose actual index has type `A_n` and whose actual star action is nontrivial is the
special unitary group `SU(B, τ)` of a central simple algebra `B` of degree `n + 1` over a
separable quadratic extension `E` of `K`, with an involution `τ` of the second kind. It
supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Quaternionic SU3Root

/-- Every affine, locally finite-type, simply connected, absolutely almost-simple group `G`
over a field `K` whose actual index `d` has type `A_n` and whose actual star action moves some
simple vertex admits a separable quadratic extension `E/K`, a central simple `E`-algebra `B` of
dimension `(n + 1)^2`, a `K`-linear involution `τ` of `B` acting on `E` by the nontrivial
automorphism of `E/K`, and a presentation `UnitaryAlgebra.Presentation E τ G` of `G` as the
special unitary group `SU(B, τ)`. -/
def OuterTypeAUnitaryAlgebraPresentationStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
    (∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      d.star σ a ≠ a) →
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra.IsQuadraticExtension K E)
      (_ : Algebra.IsSeparable K E) (B : Type u) (_ : Ring B) (_ : Algebra E B)
      (_ : Algebra K B) (_ : IsScalarTower K E B) (_ : FiniteDimensional E B)
      (_ : Algebra.IsCentral E B) (_ : IsSimpleRing B) (τ : FirstKindInvolution K B),
      (∀ x : E, τ (algebraMap E B x) = algebraMap E B (conjugation K E x)) ∧
        Module.finrank E B = (n + 1) ^ 2 ∧ Nonempty (UnitaryAlgebra.Presentation E τ G)

end Langlands.GroupScheme
