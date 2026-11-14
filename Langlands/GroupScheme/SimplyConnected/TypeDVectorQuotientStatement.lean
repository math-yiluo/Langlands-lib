import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeight
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.OrthogonalMatrix.Subgroups
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# The vector quotient of a simply connected group of type `D_n`: statement

This unproved statement records the quotient of a simply connected group of type
`D_n` (`n ≥ 4`) by the part of its centre on which the fundamental weight at the
vertex numbered `0` is trivial. When the absolute Galois star action fixes that
vertex, the quotient is defined over the ground field, it is a form of the split
special orthogonal group `SO_{2n}` over the separable closure, and the quotient map
is a central isogeny whose kernel is killed by that fundamental weight.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `K` be a field and `G` an affine group scheme of locally finite type over `K`
with an actual index `d`, numbered by `e : d.Vertex ≃ Fin n` with `n ≥ 4` so that every
Cartan entry is that of `CartanMatrix.D n`. Assume `G` is simply connected and absolutely
almost simple, and that every element of the absolute Galois group fixes, under the star
action, the vertex numbered `0`.
Then there are an affine group scheme `H` of locally finite type over `K` and a central
isogeny `p : G ⟶ H` such that

- the base change of `H` to the separable closure `K^s` is isomorphic to the identity
  component `SO_{2n}` of the split orthogonal group
  `OrthogonalMatrix.groupScheme (Fin n) K^s` of the hyperbolic form on `K^s^(2n)`;
- the fundamental weight at the vertex numbered `0` is trivial on the kernel of `p` in the
  pinning torus over `K^s`, read through all `K^s`-scheme points.

This is an unproved statement. There is no characteristic hypothesis. -/
def TypeDVectorQuotientStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (n : ℕ) (e : d.Vertex ≃ Fin n),
    4 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
    (∀ (γ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val = 0 → d.star γ a = a) →
    ∃ (H : GroupScheme (Spec (CommRingCat.of K))) (_ : IsAffineHom H.X.hom)
      (_ : LocallyOfFiniteType H.X.hom) (p : G ⟶ H),
      IsCentralIsogeny p ∧
        Nonempty ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj H ≅
          identityComponent
            (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of (SeparableClosure K)))) ∧
        ∀ v : d.Vertex, (e v).val = 0 → d.FundamentalWeightTrivialOnKernel v p

end Langlands.GroupScheme
