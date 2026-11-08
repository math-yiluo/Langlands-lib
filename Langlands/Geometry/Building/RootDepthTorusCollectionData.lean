import Langlands.Geometry.Building.RootDepthCollectionData
import Langlands.Geometry.Building.RootValueTorusCommutator
import Langlands.Geometry.Building.RootValueTorusDouble

/-! # Actual collection data for the canonical torus restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [Mono i.hom.hom.left] {φ : RootFunctionFamily T G}

/-- The canonical restricted family has the actual subgroup carriers and
commutator/doubled inclusions required for depth collection, before reflection
or opposite-root laws have been established downstairs. -/
def torusRestrictedRootDepthCollectionData
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) :
    RootDepthCollectionData (CommGroupScheme.groupHom f ≫ i)
      (torusRestrictedRootFunctionFamily hS hT hE hφ f) := by
  classical
  let H : characterLattice S → ℝ → Subgroup (rationalPoints G) := fun a r =>
    if a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)
    then torusRestrictedRootDepthSubgroup hφ f a r
    else rootGroupPoints (CommGroupScheme.groupHom f ≫ i) a
  refine { subgroup := H, coe_subgroup := ?_, commutator_le := ?_, double_le := ?_ }
  · intro a r
    by_cases ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)
    · simp only [H, ite_eq_left ha]
      exact (rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f a ha r).symm
    · simp only [H, ite_eq_right ha]
      ext g
      simp only [mem_rootFiltration, SetLike.mem_coe,
        torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots
          hS hT hE hφ f a ha g, le_top, and_true]
  · intro a ha b hb hab r s
    simp only [H, ite_eq_left ha, ite_eq_left hb]
    refine (torusRestrictedRootDepthSubgroup_commutator_le hS hφ f
      a ha b hb hab r s).trans ?_
    refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
      iSup_le fun hq => iSup_le fun hc => ?_
    refine le_iSup_of_le p (le_iSup_of_le q (le_iSup_of_le hp
      (le_iSup_of_le hq (le_iSup_of_le hc ?_))))
    rw [ite_eq_left hc]
  · intro a ha h2a r s hrs
    simp only [H, ite_eq_left ha, ite_eq_left h2a]
    exact ((torusRestrictedRootDepthSubgroup_antitone hφ f (2 • a)) hrs).trans
      (by rw [torusRestrictedRootDepthSubgroup_double_eq hS hT hE hφ f a ha.1 r]
          exact inf_le_left)

/-- On an actual lower root the collection subgroup is exactly the canonical
multiplier-scaled subgroup, with its original real depth. -/
theorem torusRestrictedRootDepthCollectionData_subgroup_eq
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (a : characterLattice S)
    (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)) (r : ℝ) :
    (torusRestrictedRootDepthCollectionData hS hT hE hφ f).subgroup a r =
      torusRestrictedRootDepthSubgroup hφ f a r := by
  classical
  simp only [torusRestrictedRootDepthCollectionData, ite_eq_left ha]

/-- Off the actual roots, support normalization makes every finite level the
whole corresponding root group. -/
theorem torusRestrictedRootDepthCollectionData_subgroup_eq_of_not_mem_roots
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (a : characterLattice S)
    (ha : a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ i)) (r : ℝ) :
    (torusRestrictedRootDepthCollectionData hS hT hE hφ f).subgroup a r =
      rootGroupPoints (CommGroupScheme.groupHom f ≫ i) a := by
  classical
  simp only [torusRestrictedRootDepthCollectionData, ite_eq_right ha]

end Langlands.Geometry.Building
