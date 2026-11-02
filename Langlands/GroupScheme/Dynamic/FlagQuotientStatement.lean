import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper dynamic flag quotients and algebraic local sections -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A proper scheme model of the dynamic parabolic quotient, with exact coset
fibers on every test scheme and algebraic sections near every rational point. -/
def DynamicFlagQuotientExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      ∃ (Q : Over (Spec (CommRingCat.of k))) (π : G.X ⟶ Q),
        IsProper Q.hom ∧
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ π = h ≫ π ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T) ∧
        ∀ p : RingPoint k Q k,
          ∃ (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X),
            Set.range p.left ⊆ U ∧ s ≫ π = openOverι k Q U

end Langlands.GroupScheme
