import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AbelianScheme.GroupScheme
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Topological group properties of actual affine group-scheme points
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

/-- The existing scheme-theoretic group law is continuous for the existing
evaluation topology on actual finite-type affine group-scheme points. -/
def AffineGroupTopologicalProperty [IsTopologicalRing S] : Prop :=
  ∀ (G : Langlands.GroupScheme (Spec (CommRingCat.of R)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    letI : Group (RingPoint R G.X S) :=
      inferInstanceAs (Group (ringTest R S ⟶ G.X))
    IsTopologicalGroup (RingPoint R G.X S)

/-- Actual group-scheme homomorphisms and isomorphisms act continuously and
homeomorphically, respectively, on the same actual point spaces. -/
def AffineGroupFunctorialProperty [IsTopologicalRing S] : Prop :=
  ∀ (G H : Langlands.GroupScheme (Spec (CommRingCat.of R)))
    [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom],
    (∀ f : G ⟶ H,
      Continuous (X := RingPoint R G.X S) (Y := RingPoint R H.X S) (fun p =>
        (p ≫ f.hom.hom : RingPoint R H.X S))) ∧
    (∀ e : G ≅ H,
      IsHomeomorph (X := RingPoint R G.X S) (Y := RingPoint R H.X S) (fun p =>
        (p ≫ e.hom.hom.hom : RingPoint R H.X S)))

/-- Closed immersions of actual affine group schemes induce subspace
embeddings, with closed image over a Hausdorff value ring. -/
def AffineGroupClosedImmersionProperty [IsTopologicalRing S] : Prop :=
  ∀ (G H : Langlands.GroupScheme (Spec (CommRingCat.of R)))
    [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (f : G ⟶ H) [IsClosedImmersion f.hom.hom.left],
    IsEmbedding (X := RingPoint R G.X S) (Y := RingPoint R H.X S) (fun p =>
      (p ≫ f.hom.hom : RingPoint R H.X S)) ∧
    ∀ [T2Space S],
      IsClosedEmbedding (X := RingPoint R G.X S) (Y := RingPoint R H.X S) (fun p =>
        (p ≫ f.hom.hom : RingPoint R H.X S))

/-- Hausdorffness and local compactness retain their separate value-ring
hypotheses on actual affine group-scheme points. -/
def AffineGroupLocalCompactnessProperty : Prop :=
  (∀ [T2Space S] (G : Langlands.GroupScheme (Spec (CommRingCat.of R)))
    [IsAffine G.X.left], T2Space (RingPoint R G.X S)) ∧
  (∀ [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of R)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    LocallyCompactSpace (RingPoint R G.X S))

/-- Source-qualified group consequences for the actual evaluation topology. -/
def AffineGroupPointProperties : Prop :=
  (∀ [IsTopologicalRing S], AffineGroupTopologicalProperty R S) ∧
  (∀ [IsTopologicalRing S], AffineGroupFunctorialProperty R S) ∧
  (∀ [IsTopologicalRing S], AffineGroupClosedImmersionProperty R S) ∧
  AffineGroupLocalCompactnessProperty R S

end Langlands.AlgebraicGeometry.PointTopology
