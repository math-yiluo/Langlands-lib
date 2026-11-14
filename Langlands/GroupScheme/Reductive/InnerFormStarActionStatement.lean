import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Reductive.StarAction
import Mathlib.FieldTheory.SeparableClosure

/-! # Statement: inner forms are detected by the star action -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Inner forms are detected by the star action** (Conrad, *Reductive group schemes*
(2014), Proposition 7.2.2, in terms of the `∗`-action of p.256). Let `G` and `G'` be affine
group schemes of locally finite type over a field `k`, let `q : G ⟶ A` be an adjoint quotient
of `G`, and let `d` and `d'` be Galois pinning data of `G` and `G'` over the separable
closure of `k`. Then `G'` is an inner form of `G`, that is, over some finite Galois
extension `L/k` there is an isomorphism of `G` and `G'` whose discrepancy on every pair of
points of `Spec L` is the action of a point of `A`, if and only if some isomorphism of the
root data of `d` and `d'` preserves the chosen bases and intertwines the two star actions. -/
def InnerFormStarActionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' A : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom]
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    (d : GaloisPinningData k (SeparableClosure k) G)
    (d' : GaloisPinningData k (SeparableClosure k) G'),
    (∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
        (_ : IsGalois k L)
        (e : LocalGroupIso G G' (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))))),
        e.HasInnerDiscrepancy hq.innerAction) ↔
      ∃ f : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum,
        (∀ a, a ∈ d.toSplitPinning.base.support ↔
          f.indexEquiv a ∈ d'.toSplitPinning.base.support) ∧
        ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
          RootPairing.Equiv.comp f (d.starAction σ).val =
            RootPairing.Equiv.comp (d'.starAction σ).val f

end Langlands.GroupScheme
