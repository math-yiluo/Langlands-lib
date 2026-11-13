import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.RelativeLevi.Borel

/-! # Statement: quasi-split inner forms of reductive groups over a semi-local base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Quasi-split inner forms over a semi-local base** (Conrad, *Reductive group schemes*
(2014), Proposition 7.2.12). Let `R` be a commutative ring with finitely many maximal ideals
and `G` a reductive group scheme over `Spec R`. Let `p : G ⟶ G_ad` be an fppf quotient of `G`
by its centre and `c` the action of `G_ad` on `G` whose restriction along `p` is conjugation.
Call `G'` an inner form of `G` if, on some étale surjective `U ⟶ Spec R`, there is an
isomorphism of `G` and `G'` over the points of `U` whose discrepancy on every pair of points
of `U` is the action of a point of `G_ad`. Then `G` has a quasi-split inner form, and any two
quasi-split inner forms of `G` are isomorphic. -/
def ReductiveSemilocalQuasiSplitInnerFormStatement : Prop :=
  ∀ (R : Type u) [CommRing R], Finite (MaximalSpectrum R) →
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

end Langlands.GroupScheme
