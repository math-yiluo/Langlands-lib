import Langlands.Cohomology.EquivariantComposite.Cofree
import Langlands.Sheaf.Equivariant.SmoothPart
import Mathlib.Topology.LocallyConstant.Basic

/-! # Compact saturations under actions with stable neighbourhoods -/

noncomputable section

open CategoryTheory TopologicalSpace Langlands.Sheaf.Equivariant

namespace Langlands.Cohomology.EquivariantComposite

universe u

variable {G X : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X]

/-- Stable neighbourhoods imply continuity of the joint action map. -/
theorem continuous_action_of_stableNeighbourhoods :
    Continuous (fun p : G × X => p.1 • p.2) := by
  constructor
  intro O hO
  apply isOpen_iff_mem_nhds.2
  rintro ⟨g, x⟩ hx
  obtain ⟨H, V, hV, hxV, hVO, hHV⟩ :=
    HasStableNeighbourhoods.exists_stable (G := G) x
      ((fun y : X => g • y) ⁻¹' O) (hO.preimage (continuous_const_smul g)) hx
  let N : Set G := (fun k : G => g⁻¹ * k) ⁻¹' (H : Set G)
  have hN : IsOpen N := H.isOpen.preimage (continuous_const_mul g⁻¹)
  have hgN : g ∈ N := by simp [N]
  apply Filter.mem_of_superset ((hN.prod hV).mem_nhds ⟨hgN, hxV⟩)
  rintro ⟨k, y⟩ ⟨hk, hy⟩
  have ht := hVO (hHV (g⁻¹ * k) hk y hy)
  simpa only [Set.mem_preimage, smul_smul, mul_inv_cancel_left] using ht

/-- The union of all group translates of a subset. -/
def compactSaturation (K : Set X) : Set X :=
  (fun p : G × X => p.1 • p.2) '' (Set.univ ×ˢ K)

/-- Compactness of the group makes the saturation of a compact set compact. -/
theorem isCompact_compactSaturation [CompactSpace G] {K : Set X} (hK : IsCompact K) :
    IsCompact (compactSaturation (G := G) K) :=
  (isCompact_univ.prod hK).image continuous_action_of_stableNeighbourhoods

variable {R : Type u} [CommRing R]

/-- A uniformly smooth function on a topological group is locally constant. -/
theorem cofree_isLocallyConstant (M : ModuleCat.{u} R) (s : cofreeObj R G M) :
    IsLocallyConstant s.val := by
  obtain ⟨H, hH⟩ := s.property
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  refine ⟨(fun k : G => k * g⁻¹) ⁻¹' (H : Set G),
    H.isOpen.preimage (continuous_mul_const g⁻¹), ?_, ?_⟩
  · simp
  · intro k hk
    have h := congrFun (hH ⟨(k * g⁻¹)⁻¹, H.inv_mem hk⟩) g
    change s.val (((k * g⁻¹)⁻¹)⁻¹ * g) = s.val g at h
    simpa using h

/-- A uniformly smooth function on a compact group has finite range. -/
theorem cofree_finite_range [CompactSpace G] (M : ModuleCat.{u} R)
    (s : cofreeObj R G M) : (Set.range s.val).Finite :=
  (cofree_isLocallyConstant M s).range_finite

end Langlands.Cohomology.EquivariantComposite
