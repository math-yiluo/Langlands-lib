import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.MvPolynomial.Basic
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.RelativeLevi.Borel

/-! # Statement: quasi-split inner forms over bases with trivial Picard groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Quasi-split inner forms over `Spec ℤ`, affine spaces and bases with trivial Picard
groups** (Conrad, *Reductive group schemes* (2014), Remark 7.2.13, extending
Proposition 7.2.12). For a commutative ring `R`, let `QSInner R` say: for every reductive
group scheme `G` over `Spec R`, every fppf quotient `p : G ⟶ G_ad` of `G` by its centre and
the action `c` of `G_ad` on `G` whose restriction along `p` is conjugation, `G` has a
quasi-split inner form, and any two quasi-split inner forms of `G` are isomorphic. Here `G'`
is an inner form of `G` if, on some étale surjective `U ⟶ Spec R`, there is an isomorphism of
`G` and `G'` over the points of `U` whose discrepancy on every pair of points of `U` is the
action of a point of `G_ad`. Then `QSInner R` holds

1. whenever every finite étale `R`-algebra has trivial Picard group;
2. whenever `R` is isomorphic to `ℤ`;
3. for every polynomial ring `k[x₁, …, xₙ]` over a field `k` of characteristic zero. -/
def ReductivePicardTrivialQuasiSplitInnerFormStatement : Prop :=
  let QSInner : ∀ (R : Type u) [CommRing R], Prop := fun R _ =>
    ∀ G : GroupScheme (Spec (CommRingCat.of R)), IsReductive G →
    ∀ (Gad : GroupScheme (Spec (CommRingCat.of R))) (p : G ⟶ Gad),
      RelativeRoot.IsFppfQuotient (center G) p →
    ∀ c : AutomorphicAction Gad G, c.restrict p = AutomorphicAction.conjugation (𝟙 G) →
    let IsInnerForm : GroupScheme (Spec (CommRingCat.of R)) → Prop := fun G' =>
      ∃ U : Over (Spec (CommRingCat.of R)), Etale U.hom ∧ Surjective U.hom ∧
        ∃ e : LocalGroupIso G G' U, e.HasInnerDiscrepancy c
    (∃ G' : GroupScheme (Spec (CommRingCat.of R)), IsRelativeQuasiSplit G' ∧ IsInnerForm G') ∧
    ∀ G₁ G₂ : GroupScheme (Spec (CommRingCat.of R)),
      IsRelativeQuasiSplit G₁ → IsInnerForm G₁ →
      IsRelativeQuasiSplit G₂ → IsInnerForm G₂ → Nonempty (G₁ ≅ G₂)
  (∀ (R : Type u) [CommRing R],
      (∀ (R' : Type u) [CommRing R'] [Algebra R R'], Algebra.Etale R R' →
        Module.Finite R R' → Subsingleton (CommRing.Pic R')) →
      QSInner R) ∧
    (∀ (R : Type u) [CommRing R], Nonempty (R ≃+* ℤ) → QSInner R) ∧
    ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ), QSInner (MvPolynomial (Fin n) k)

end Langlands.GroupScheme
