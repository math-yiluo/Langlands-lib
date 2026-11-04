import Langlands.Geometry.Building.ValuationBuildingData
import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.Geometry.Building.FilteredRootProducts
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactness
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Compact open root filtrations in the canonical topology
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance kpFiltrationTopologyAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance kpFiltrationTopologyAmbientTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

variable (B : ValuationBuildingData G)

/-- An actual relative root group is closed in the canonical ambient topology. -/
theorem isClosed_rootGroup (a : relativeRoots B.i) :
    IsClosed (B.rootGroup a : Set (rationalPoints G)) := by
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  obtain ⟨U, j, hj, hc, _, _⟩ :=
    RelativeRoot.subgroup_has_smooth_closed_representative
      B.isMaximalSplitTorus.isSplitSubtorus.1 B.i a a.property.1
  exact isClosed_rationalPoint_subgroup F (RelativeRoot.subgroup B.i a) j hj hc

variable (hB : B.apartment.IsTopologyCompatible)

include hB

/-- V 7 packages the actual filtration as an open subgroup of its root group.
The topology on the root group is the subspace topology from the canonical
rational-point topology of `G`. -/
def filtrationOpenSubgroup (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    OpenSubgroup (B.rootGroup a) where
  toSubgroup := (B.filtration x a r).subgroupOf (B.rootGroup a)
  isOpen' := ((hB x.val x.mem a a.property).2 r).1

@[simp] theorem coe_filtrationOpenSubgroup
    (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    (B.filtrationOpenSubgroup hB x a r : Set (B.rootGroup a)) =
      ((↑) : B.rootGroup a → rationalPoints G) ⁻¹'
        (B.filtration x a r : Set (rationalPoints G)) := rfl

/-- Relative openness and the closed root-group embedding make each actual
root filtration closed in the ambient rational-point group. -/
theorem isClosed_filtration (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    IsClosed (B.filtration x a r : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have he := (B.isClosed_rootGroup a).isClosedEmbedding_subtypeVal
  refine (he.isClosed_iff_preimage_isClosed ?_).2 ?_
  · intro g hg
    exact ⟨⟨g, B.filtration_le_rootGroup x a r hg⟩, rfl⟩
  · exact (B.filtrationOpenSubgroup hB x a r).isClosed

/-- Each actual root filtration is compact as a subset of `G(F)`.
The proof uses V 7 boundedness and the local-field affine compactness comparison. -/
theorem isCompact_filtration (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    IsCompact (B.filtration x a r : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  exact (localFieldAffineBoundedCompactness_proof F G.X _
    (B.isClosed_filtration hB x a r)).1 ((hB x.val x.mem a a.property).2 r).2

/-- The open subgroup supplied by V 7 is compact in the root-group topology. -/
theorem isCompact_filtrationOpenSubgroup
    (x : B.Apartment) (a : relativeRoots B.i) (r : ℝ) :
    IsCompact (B.filtrationOpenSubgroup hB x a r : Set (B.rootGroup a)) :=
  (B.isClosed_rootGroup a).isClosedEmbedding_subtypeVal.isCompact_preimage
    (B.isCompact_filtration hB x a r)

/-- The doubled-root filtration is compact, including its trivial-group
convention when twice the character is not a relative root. -/
theorem isCompact_doubleFiltration
    (x : B.Apartment) (a : characterLattice B.S) (r : ℝ) :
    IsCompact (B.apartment.doubleFiltration x a r : Set (rationalPoints G)) := by
  classical
  by_cases ha : 2 • a ∈ relativeRoots B.i
  · rw [B.apartment.doubleFiltration_of_mem x a r ha]
    exact B.isCompact_filtration hB x ⟨2 • a, ha⟩ r
  · rw [B.apartment.doubleFiltration_of_not_mem x a r ha]
    simpa only [Subgroup.coe_bot] using isCompact_singleton (x := (1 : rationalPoints G))

/-- Both factors of the actual real-depth root block are retained.
Their set product is compact in the canonical ambient topology. -/
theorem isCompact_filtrationBlock
    (x : B.Apartment) (f : characterLattice B.S → ℝ) (a : relativeRoots B.i) :
    IsCompact (B.apartment.filtrationBlock x f a) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact (B.isCompact_filtration hB x a (f a)).mul
    (B.isCompact_doubleFiltration hB x a (f (2 • (a : characterLattice B.S))))

end Langlands.Geometry.Building.ValuationBuildingData
