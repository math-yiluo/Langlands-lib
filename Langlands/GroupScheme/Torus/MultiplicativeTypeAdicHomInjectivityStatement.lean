import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Statement: homomorphisms from isotrivial groups of multiplicative type are determined by their reductions modulo powers of an ideal -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- SGA 3, Exposé IX, Théorème 7.1, injectivity part. Let `A` be a noetherian ring, separated
and complete for the `I`-adic topology of an ideal `I`, let `S = Spec A` and
`Sₙ = Spec (A / I ^ (n + 1))`. Let `H` be an `S`-group that becomes diagonalizable over a
finite étale surjective `S' ⟶ S`, and let `G` be an affine `S`-group. Two homomorphisms
`u, u' : H ⟶ G` whose base changes to `Sₙ` agree for every `n` are equal. -/
def MultiplicativeTypeAdicHomInjectivityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsAffineHom G.X.hom],
    (∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H)) →
      ∀ u u' : H ⟶ G,
        (∀ n : ℕ,
          (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).map u =
            (GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).map u') →
          u = u'

end Langlands.GroupScheme
