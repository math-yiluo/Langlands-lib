import Langlands.Topology.LocallyProfinite
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed

/-! # Renard II.3.3–II.3.4: orbit maps and locally profinite quotients -/

set_option autoImplicit false

universe uG uX

namespace Langlands.Topology.RenardOrbitQuotient

/-- The open-orbit assertion includes the necessary nonemptiness condition.
The map to the ambient space is open because its orbit is open. -/
def FiniteOrbitOpenOrbitStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G]
    (X : Type uX) [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [Nonempty X],
    IsLocallyProfinite G → IsLocallyProfinite X →
    Finite (Quotient (MulAction.orbitRel G X)) →
      ∃ x : X, IsOpen (MulAction.orbit G x) ∧
        ∀ y ∈ MulAction.orbit G x, IsOpenMap (fun g : G => g • y)

/-- The last sentence of II.3.3's Proposition, including the empty-space case. -/
def FiniteOrbitsLocallyClosedStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G]
    (X : Type uX) [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X],
    IsLocallyProfinite G → IsLocallyProfinite X →
    Finite (Quotient (MulAction.orbitRel G X)) →
      ∀ x : X, IsLocallyClosed (MulAction.orbit G x)

/-- Invariant closed and locally closed sets descend to the actual orbit quotient. -/
def InvariantQuotientImagesStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type uX) [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X],
    IsLocallyProfinite G → IsLocallyProfinite X →
      ∀ Z : Set X, (∀ (g : G) (x : X), x ∈ Z → g • x ∈ Z) →
        (IsClosed Z →
          IsClosed ((Quotient.mk (MulAction.orbitRel G X)) '' Z)) ∧
        (IsLocallyClosed Z →
          IsLocallyClosed ((Quotient.mk (MulAction.orbitRel G X)) '' Z))

/-- The paragraph after the II.3.3 Lemma: a Hausdorff orbit quotient is t.d. -/
def HausdorffOrbitQuotientStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type uX) [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X],
    IsLocallyProfinite G → IsLocallyProfinite X →
      T2Space (Quotient (MulAction.orbitRel G X)) →
        IsLocallyProfinite (Quotient (MulAction.orbitRel G X))

/-- The II.3.3 Corollary identifies the canonical map, not just the two spaces. -/
def TransitiveQuotientHomeomorphismStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G]
    (X : Type uX) [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [MulAction.IsPretransitive G X],
    IsLocallyProfinite G → IsLocallyProfinite X →
      ∀ x : X, ∃ e : (G ⧸ MulAction.stabilizer G x) ≃ₜ X,
        ∀ g : G, e (QuotientGroup.mk g) = g • x

/-- II.3.4, without a normality assumption on the closed subgroup. -/
def ClosedSubgroupQuotientStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ N : Subgroup G, IsClosed (N : Set G) → IsLocallyProfinite (G ⧸ N)

/-- All new topology targets; openness of the orbit projection itself is
already proved by Mathlib's `MulAction.isOpenQuotientMap_quotientMk`. -/
def Statements : Prop :=
  FiniteOrbitOpenOrbitStatement.{uG, uX} ∧
    FiniteOrbitsLocallyClosedStatement.{uG, uX} ∧
    InvariantQuotientImagesStatement.{uG, uX} ∧
    HausdorffOrbitQuotientStatement.{uG, uX} ∧
    TransitiveQuotientHomeomorphismStatement.{uG, uX} ∧
    ClosedSubgroupQuotientStatement.{uG}

end Langlands.Topology.RenardOrbitQuotient
