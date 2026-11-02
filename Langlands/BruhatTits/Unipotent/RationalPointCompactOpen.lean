import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Compact open subgroups of actual rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter Set
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits

section Ring

variable (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]

local instance : TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X
/-- The evaluation embedding transfers total disconnectedness from the value ring. -/
theorem rationalPoint_totallyDisconnectedSpace [TotallyDisconnectedSpace R] :
    TotallyDisconnectedSpace (RationalPoint R G.X) := by
  let e := ((AlgPoint.isEmbedding_evaluation (R := R)
    (A := AffineCoordinateRing R G.X) (S := R)).comp
      (affineSchemePointHomeomorph R G.X R).isEmbedding).comp
        (rationalPointHomeomorph R G.X).isEmbedding
  exact e.isTotallyDisconnected_range.mp (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end Ring

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- The given nonarchimedean local-field topology is Hausdorff. -/
theorem localField_t2Space : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/-- The given nonarchimedean local-field topology is totally disconnected. -/
theorem localField_totallyDisconnectedSpace : TotallyDisconnectedSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let : T2Space F := inferInstance
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

variable (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

/-- Actual finite-type affine group rational points over a local field are locally profinite. -/
theorem rationalPoint_isLocallyProfinite :
    Langlands.Topology.IsLocallyProfinite (RationalPoint F G.X) := by
  let : T2Space F := localField_t2Space F
  let : TotallyDisconnectedSpace F := localField_totallyDisconnectedSpace F
  let : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
  let : LocallyCompactSpace (RationalPoint F G.X) := rationalPoint_locallyCompactSpace F G
  let : TotallyDisconnectedSpace (RationalPoint F G.X) :=
    rationalPoint_totallyDisconnectedSpace F G
  exact Langlands.Topology.isLocallyProfinite_of_mathlib

/-- Van Dantzig supplies a compact open subgroup of the actual rational-point group. -/
theorem rationalPoint_exists_compactOpenSubgroup :
    ∃ K : OpenSubgroup (RationalPoint F G.X),
      IsCompact (K : Set (RationalPoint F G.X)) := by
  let : IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
  obtain ⟨K, hK, _⟩ :=
    (Langlands.Topology.LocallyProfiniteProof.vanDantzig (RationalPoint F G.X)).mp
      (rationalPoint_isLocallyProfinite F G) |>.2 Set.univ Filter.univ_mem
  exact ⟨K, hK⟩

/-- A compact open subgroup of the actual rational-point group, with its compactness proof. -/
def rationalPointCompactOpenSubgroup :
    {K : OpenSubgroup (RationalPoint F G.X) //
      IsCompact (K : Set (RationalPoint F G.X))} :=
  ⟨(rationalPoint_exists_compactOpenSubgroup F G).choose,
    (rationalPoint_exists_compactOpenSubgroup F G).choose_spec⟩

end LocalField

end Langlands.BruhatTits
