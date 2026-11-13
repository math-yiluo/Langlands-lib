import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicInnerTypeAStatement
import Langlands.GroupScheme.Examples.HermitianRootGroupScheme

/-!
# Local outer forms of type A are Hermitian models with a hyperbolic plane

This module states, on actual Tits-index data, that over a nonarchimedean local
field every simply connected absolutely almost-simple group whose index has type
`A_n` and a nontrivial actual star action is isomorphic to the Library's actual
weighted Hermitian group scheme: a hyperbolic plane plus a diagonal nondegenerate
Hermitian middle of dimension `n - 1`, for a separable quadratic extension of the
base field. It supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a nonarchimedean local field, an affine simply connected absolutely
almost-simple group whose actual index has type `A_n` and whose actual star action
moves some simple vertex is isomorphic to the actual Hermitian model
`HermitianRoot.SchemeModel.groupScheme K L H w hw`, for some separable quadratic
extension `L` of `K` and some diagonal Hermitian form `H` on `L^(n - 1)` whose
weights are the units `w`. No anisotropy of `G` and no anisotropy of `H` is
asserted or assumed. -/
def LocalOuterTypeAHermitianModelStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
      (∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
        d.star σ a ≠ a) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsQuadraticExtension K L) (_ : Algebra.IsSeparable K L)
        (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution K L) (Fin (n - 1)))
        (w : Fin (n - 1) → Lˣ) (hw : ∀ i, (w i : L) = H.weight i),
        Nonempty (G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw)

end Langlands.GroupScheme
