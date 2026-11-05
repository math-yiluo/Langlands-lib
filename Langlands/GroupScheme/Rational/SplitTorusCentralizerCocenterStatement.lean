import Langlands.GroupScheme.Torus.Induced
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Derived.Basic

/-! # Cocenters of split-torus centralizers in simply connected groups are induced -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The proposition that, in a simply connected group `G` over a field `k`, if `M = Z_G(A)` is
the centralizer of a split subtorus `A` and `d : D → M` exhibits its derived subgroup, then every
commutative fppf quotient `q : M → D'` with kernel `D` is an induced torus (KP Definition 2.5.1).
-/
def SplitTorusCentralizerCocenterInducedStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsSimplyConnected G →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G), IsSplitSubtorus a →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (torusCentralizer a).IsRepresentedBy j →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M), IsDerivedSubgroup d →
    ∀ (D' : CommGroupScheme (Spec (CommRingCat.of k))) (q : M ⟶ D'.toGrp),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q → IsInducedTorus D'

end Langlands.GroupScheme
