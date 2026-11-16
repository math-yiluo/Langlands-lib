import Langlands.BruhatTits.Cartan.RenardLeviCones
import Langlands.GroupScheme.Rational.StandardParabolic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Topology of Renard's chamber in the actual split-component space

The chamber of V.3.15 is nonempty and open in the canonical real module topology;
its closure is the published nonstrict chamber used in V.3.21. The hypotheses
specify the actual standard Levi, its split component and the inclusion factor.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.Cartan.RenardLeviCones

/-- Renard V.3.15, with the topological meaning of the closure notation made
explicit on `𝔞_M = V A`. Nonemptiness is a conclusion for the actual standard-Levi
data, including the case of no simple roots outside `J`. -/
def LeviChamberTopologyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
    ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j → (standardLevi i ν J).IsRepresentedBy j →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ L),
      IsSplitComponent a →
    ∀ f : A ⟶ T, CommGroupScheme.groupHom f ≫ i = a ≫ j →
      letI : TopologicalSpace (V A) := moduleTopology ℝ (V A)
      (chamber i ν J f).Nonempty ∧
      IsOpen (chamber i ν J f) ∧
      IsClosed (closedChamber i ν J f) ∧
      closure (chamber i ν J f) = closedChamber i ν J f

end Langlands.BruhatTits.Cartan.RenardLeviCones
