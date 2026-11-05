import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer

/-!
# `G(k) = G(k)^♮ · Z_G(S)(k)` (KP Fact 2.6.22)

Statement, not proof, for the minimal Levi subgroup `Z_G(S)` of a maximal split torus `S`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- KP Fact 2.6.22 for the minimal Levi subgroup: for a connected reductive group `G` over a
field `k` with simply connected cover `π : C → D` of its derived subgroup `d : D → G`, a
maximal split torus `i : S → G` and its centralizer `j : Z → G`, every `g ∈ G(k)` is a
product `g = h · j(z)` of an element `h` of the image `G(k)^♮` of `C(k) → G(k)` and an
element `z ∈ Z(k)`. -/
def SimplyConnectedCentralizerProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (G Z C D : GroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (d : D ⟶ G) (π : C ⟶ D),
    IsSimplyConnectedDerivedCover d π → IsMaximalSplitTorus i →
      (torusCentralizer i).IsRepresentedBy j →
      ∀ g : rationalPoints G, ∃ c : rationalPoints C, ∃ z : rationalPoints Z,
        g = rationalPoints.map (π ≫ d) c * rationalPoints.map j z

end Langlands.GroupScheme
