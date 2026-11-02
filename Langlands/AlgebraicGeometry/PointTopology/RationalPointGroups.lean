import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineGroupProofs
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Group operations on identity-test rational points
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable (G : Langlands.GroupScheme (Spec (CommRingCat.of R)))

local instance : Group (RingPoint R G.X R) :=
  inferInstanceAs (Group (ringTest R R ⟶ G.X))

/-- The identity-test point comparison preserves the existing Hom group law. -/
def rationalPointGroupEquiv :
    RationalPoint R G.X ≃* RingPoint R G.X R where
  __ := rationalPointEquiv R G.X
  map_mul' p q := by
    simp only [rationalPointEquiv]
    rfl

@[simp] theorem rationalPointGroupEquiv_apply (p : RationalPoint R G.X) :
    rationalPointGroupEquiv R G p = rationalPointEquiv R G.X p := rfl

variable [TopologicalSpace R] [IsAffine G.X.left]

/-- The group comparison is a homeomorphism for the canonical named topology. -/
def rationalPointGroupHomeomorph :
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    RationalPoint R G.X ≃ₜ* RingPoint R G.X R := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  exact { rationalPointGroupEquiv R G, rationalPointHomeomorph R G.X with }

/-- The canonical identity-test topology makes the actual Hom group topological. -/
theorem rationalPoint_isTopologicalGroup [IsTopologicalRing R]
    [LocallyOfFiniteType G.X.hom] :
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    IsTopologicalGroup (RationalPoint R G.X) := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  let : IsTopologicalGroup (RingPoint R G.X R) := affineGroupTopological_proof R R G
  exact (rationalPointHomeomorph R G.X).isInducing.isTopologicalGroup
    (rationalPointGroupEquiv R G)

/-- Inversion on actual identity-test rational points is continuous. -/
theorem continuous_rationalPoint_inv [IsTopologicalRing R]
    [LocallyOfFiniteType G.X.hom] :
    let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    Continuous (fun p : RationalPoint R G.X => p⁻¹) := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  let : IsTopologicalGroup (RationalPoint R G.X) := rationalPoint_isTopologicalGroup R G
  exact continuous_inv

/-- Hausdorffness transfers without finiteness or continuity hypotheses. -/
theorem rationalPoint_t2Space [T2Space R] :
    letI : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    T2Space (RationalPoint R G.X) := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  let : T2Space (RingPoint R G.X R) :=
    (affineGroupLocalCompactness_proof R R).1 G
  exact (rationalPointHomeomorph R G.X).isEmbedding.t2Space

/-- Local compactness transfers for finite-type affine group points. -/
theorem rationalPoint_locallyCompactSpace [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [LocallyOfFiniteType G.X.hom] :
    letI : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
    LocallyCompactSpace (RationalPoint R G.X) := by
  let : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
  let : LocallyCompactSpace (RingPoint R G.X R) :=
    (affineGroupLocalCompactness_proof R R).2 G
  exact (rationalPointHomeomorph R G.X).isClosedEmbedding.locallyCompactSpace

end Langlands.AlgebraicGeometry.PointTopology
