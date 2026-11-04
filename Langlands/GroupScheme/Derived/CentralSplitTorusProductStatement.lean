import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Derived and central split factors of a maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Multiplication of the supplied derived maximal split torus and central split
component is a central isogeny onto the ambient maximal split torus. -/
def DerivedCentralSplitTorusProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d →
    ∀ (S S_D A : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : S.toGrp ⟶ G) (j : S_D.toGrp ⟶ D) (e : S_D ⟶ S)
      (a : A.toGrp ⟶ G) (c : A ⟶ S),
      IsMaximalSplitTorus i → IsMaximalSplitTorus j →
      IsClosedSubgroup (CommGroupScheme.groupHom e) →
      j ≫ d = CommGroupScheme.groupHom e ≫ i →
      IsSplitComponent a → CommGroupScheme.groupHom c ≫ i = a →
      IsCentralIsogeny
        (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
          (fun _ _ _ => Commute.all _ _))

end Langlands.GroupScheme
