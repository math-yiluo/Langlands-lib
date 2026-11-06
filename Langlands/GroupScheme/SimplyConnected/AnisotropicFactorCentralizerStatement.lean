import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Rational.TorusCentralizer

/-!
# Anisotropic almost-simple factors centralize the maximal split torus

In a simply connected group over a field, every anisotropic closed normal almost-simple
subgroup centralizes a maximal split torus.
This module states a proposition and supplies no proof of it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over any field `k`, for a simply connected group `G` with maximal split torus `S`, every
point of an anisotropic closed normal almost-simple subgroup `a : A ⟶ G`, on every test
scheme, lies in the centralizer functor of `S`. -/
def SimplyConnectedAnisotropicFactorCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsSimplyConnected G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
      IsAlmostSimple A → IsClosedSubgroup a → (SubgroupFunctor.range a).IsNormal →
      IsAnisotropic A →
      SubgroupFunctor.range a ≤ torusCentralizer i

end Langlands.GroupScheme
