import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Mathlib.Topology.Maps.Proper.Basic

/-! # Topological restriction to a closed standard Levi -/

noncomputable section

universe u

open Topology
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section TopologicalGroups

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Forget the ambient subgroup in which an intersection is read. -/
def subgroupOfToAmbient (U L : Subgroup G) : U.subgroupOf L →* U where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_subgroupOfToAmbient (U L : Subgroup G) :
    Continuous (subgroupOfToAmbient U L) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem isEmbedding_subgroupOfToAmbient (U L : Subgroup G) :
    IsEmbedding (subgroupOfToAmbient U L) := by
  apply (IsEmbedding.subtypeVal : IsEmbedding (fun x : U => (x : G))).of_comp_iff.mp
  change IsEmbedding ((fun x : L => (x : G)) ∘
    (fun x : U.subgroupOf L => (x : L)))
  exact (IsEmbedding.subtypeVal : IsEmbedding (fun x : L => (x : G))).comp
    (IsEmbedding.subtypeVal : IsEmbedding (fun x : U.subgroupOf L => (x : L)))

/-- Intersect a subgroup of `U` with `L`, retaining the literal
`U.subgroupOf L` carrier. -/
def restrictedCompactSubgroup (U L : Subgroup G) (K : Subgroup U) :
    Subgroup (U.subgroupOf L) :=
  K.comap (subgroupOfToAmbient U L)

theorem isClosedEmbedding_subgroupOfToAmbient (U L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    IsClosedEmbedding (subgroupOfToAmbient U L) := by
  refine ⟨?_, ?_⟩
  · exact isEmbedding_subgroupOfToAmbient U L
  · have hrange : Set.range (subgroupOfToAmbient U L) =
        (fun x : U => (x : G)) ⁻¹' (L : Set G) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.val.property
      · intro hx
        exact ⟨⟨⟨x.val, hx⟩, x.property⟩, rfl⟩
    rw [hrange]
    exact hL.preimage continuous_subtype_val

theorem isCompact_restrictedCompactSubgroup (U L : Subgroup G)
    (hL : IsClosed (L : Set G)) (K : Subgroup U)
    (hK : IsCompact (K : Set U)) :
    IsCompact (restrictedCompactSubgroup U L K : Set (U.subgroupOf L)) :=
  (isClosedEmbedding_subgroupOfToAmbient U L hL).isCompact_preimage hK

/-- The compact-subgroup limit condition survives intersection with a closed
ambient subgroup. No compactness or openness of that ambient subgroup is needed. -/
theorem isLimitOfCompactSubgroups_subgroupOf (U L : Subgroup G)
    (hL : IsClosed (L : Set G))
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (U.subgroupOf L) := by
  intro C hC
  obtain ⟨K, hK, hCK⟩ := hU ((subgroupOfToAmbient U L) '' C)
    (hC.image (continuous_subgroupOfToAmbient U L))
  refine ⟨restrictedCompactSubgroup U L K,
    isCompact_restrictedCompactSubgroup U L hL K hK, ?_⟩
  intro x hx
  exact hCK ⟨x, hx, rfl⟩

namespace IsSemidirectDecomposition

variable {P M U L : Subgroup G}
  (h : IsSemidirectDecomposition P M U)
  (hL : IsSemidirectDecomposition (P.subgroupOf L)
    (M.subgroupOf L) (U.subgroupOf L))

omit [TopologicalSpace G] in
/-- The restricted projection agrees with the ambient projection on the
underlying element. The uniqueness characterization makes this independent
of how either decomposition was obtained. -/
theorem projection_subgroupOf (p : P.subgroupOf L) :
    subgroupOfToAmbient M L (hL.projection p) =
      h.projection (subgroupOfToAmbient P L p) := by
  symm
  apply (h.projection_eq_iff _ _).mpr
  exact hL.projection_inv_mul_mem p

/-- Continuity of the ambient Levi projection implies continuity of the
projection read inside any subgroup admitting the restricted decomposition. -/
theorem continuous_projection_subgroupOf (hproj : Continuous h.projection) :
    Continuous hL.projection := by
  apply (isEmbedding_subgroupOfToAmbient M L).continuous_iff.mpr
  simpa only [Function.comp_def, projection_subgroupOf h hL] using
    hproj.comp (continuous_subgroupOfToAmbient P L)

end IsSemidirectDecomposition

end TopologicalGroups

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The compact-limit hypothesis for each ambient standard unipotent
subgroup restricts to the literal family inside a closed standard Levi. -/
theorem standardLeviUnipotent_isLimitOfCompactSubgroups
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
    (J : Finset (SimpleRoot i ν))
    (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
    (I : Finset J) :
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) :=
  isLimitOfCompactSubgroups_subgroupOf _ _ hM (hUc (leviIndex J I))

/-- Continuity of the actual ambient standard projections supplies the
inside-Levi continuity premise, without a new geometric hypothesis. -/
theorem continuous_standardLeviProjection
    (hStandard : StandardCocharacterStatement.{u})
    (hInter : StandardLeviIntersectionStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (hproj : ∀ I, Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    Continuous (standardLeviProjection i ν hInter hG hi hν J I) :=
  IsSemidirectDecomposition.continuous_projection_subgroupOf
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (leviIndex J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hproj (leviIndex J I))

end RationalPointFamily

end Langlands.Aubert.General
