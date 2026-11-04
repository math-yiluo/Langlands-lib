import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Bases

/-!
# Second countability of finite-type local point spaces

Derived finite-coordinate and finite-affine-cover consequences of Conrad's
Propositions 2.1 and 3.1, used in Section 4's countable-base assertion.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- Finite-type algebra-map points are second countable in the evaluation topology. -/
def AffineAlgebraPointSecondCountability [IsTopologicalRing S] [SecondCountableTopology S] : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A],
    SecondCountableTopology (AlgPoint R A S)

/-- Finite-type affine scheme points are second countable in the affine topology. -/
def AffineSchemePointSecondCountability [IsTopologicalRing S] [SecondCountableTopology S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom], SecondCountableTopology (RingPoint R X S)

/-- Finite-type actual scheme points over a local value ring with open units
and continuous inversion are second countable in the affine-chart final topology. -/
def SchemePointSecondCountability [IsTopologicalRing S] [SecondCountableTopology S]
    [IsLocalRing S] [IsOpenUnits S] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom],
      @SecondCountableTopology (RingPoint R X S) (schemePointTopology R X S)

/-- The affine consequences and the local-value-ring finite-type gluing result. -/
def PointSecondCountabilityStatement [IsTopologicalRing S] [SecondCountableTopology S] : Prop :=
  AffineAlgebraPointSecondCountability R S ∧
    AffineSchemePointSecondCountability R S ∧
      ∀ [IsLocalRing S] [IsOpenUnits S], SchemePointSecondCountability R S

end Langlands.AlgebraicGeometry.PointTopology
