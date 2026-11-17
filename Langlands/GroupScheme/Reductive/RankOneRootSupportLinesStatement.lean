import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Statements: local rank-one root support and root-space lines -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Actual signed-pair root support and the two root-space lines under the
exact hypotheses of the split rank-one root-cell statement. -/
def SplitRankOneRootSupportLinesStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ (i : T.toGrp ⟶ G), IsMaximalTorus i →
    ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG.isAffineHom
        ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
      ∀ r : J,
        haveI := hG.isAffineHom
        (∀ β ∈ roots i, β = P.root r ∨ β = -P.root r) ∧
          Nonempty (k ≃ₗ[k] weightSpace i (P.root r)) ∧
          Nonempty (k ≃ₗ[k] weightSpace i (-P.root r))

/-- The algebraically closed geometric case of the same pointwise input.
The supplied root datum and all the original rank-one hypotheses are retained. -/
def AlgClosedRankOneRootSupportLinesStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ (i : T.toGrp ⟶ G), IsMaximalTorus i →
    ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG.isAffineHom
        ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
      ∀ r : J,
        haveI := hG.isAffineHom
        (∀ β ∈ roots i, β = P.root r ∨ β = -P.root r) ∧
          Nonempty (k ≃ₗ[k] weightSpace i (P.root r)) ∧
          Nonempty (k ≃ₗ[k] weightSpace i (-P.root r))

end Langlands.GroupScheme
