import Langlands.Representation.Smooth.Admissibility.RationalHoweJointAssemblyProof
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.Representation.Jacquet.LocalizationExactnessStatement

/-! # Local structural inputs for the standard fixed-vector argument -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Jacquet

variable {H : Type u} [Group H] [TopologicalSpace H]

/-- Compact-open containment passes from a subgroup to an ambiently closed
subgroup contained in it, with both inherited topologies. -/
theorem compactOpenContainment_of_closed_subgroup
    {N U : Subgroup H} (hN : IsClosed (N : Set H)) (hNU : N ≤ U)
    (hU : ∀ C : Set U, IsCompact C →
      ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ C ⊆ (K : Set U))
    (C : Set N) (hC : IsCompact C) :
    ∃ K : OpenSubgroup N, IsCompact (K : Set N) ∧ C ⊆ (K : Set N) := by
  let f : N →* U := Subgroup.inclusion hNU
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  obtain ⟨K, hK, hCK⟩ := hU (f '' C) (hC.image hf)
  refine ⟨K.comap f hf, ?_, fun x hx => hCK ⟨x, hx, rfl⟩⟩
  have heq : (K.comap f hf : Set N) =
      N.subtype ⁻¹' (U.subtype '' (K : Set U)) := by
    ext x
    constructor
    · intro hx
      exact ⟨f x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have hyx : y = f x := Subtype.ext he
      change f x ∈ K
      rw [← hyx]
      exact hy
  rw [heq]
  exact hN.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hK.image continuous_subtype_val)

end Langlands.Jacquet

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))

section Closedness

variable [TopologicalSpace F] [T2Space F]

/-- Actual standard Levi points are closed for the canonical point topology.
No standard-cocharacter comparison is required. -/
theorem isClosed_standardLeviPoints :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsClosed (standardLeviPoints i ν J : Set (rationalPoints G)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact isClosed_rationalPoint_subgroup F (standardLevi i ν J)
    (Standard.leviHom i ν J) (Standard.isRepresentedBy_leviHom i ν J)
    (Standard.isClosedSubgroup_leviHom i ν J)

/-- Actual standard unipotent points are closed for the canonical point
topology, including when the family of standard cocharacters is empty. -/
theorem isClosed_standardUnipotentPoints :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsClosed (standardUnipotentPoints i ν J : Set (rationalPoints G)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact isClosed_rationalPoint_subgroup F (standardUnipotent i ν J)
    (Standard.unipotentHom i ν J) (Standard.isRepresentedBy_unipotentHom i ν J)
    (Standard.isClosedSubgroup_unipotentHom i ν J)

end Closedness

section CompactContainment

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- One local standard cocharacter suffices for compact-open containment in
the actual standard unipotent subgroup. Only its inclusion into the dynamic
unipotent subgroup is used. -/
theorem standardUnipotentPoints_compactOpenContainment
    (hG : IsConnectedReductive G)
    (hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ C : Set (standardUnipotentPoints i ν J), IsCompact C →
      ∃ K : OpenSubgroup (standardUnipotentPoints i ν J),
        IsCompact (K : Set (standardUnipotentPoints i ν J)) ∧
          C ⊆ (K : Set (standardUnipotentPoints i ν J)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  obtain ⟨zeta, hzeta⟩ := hstandard
  exact Langlands.Jacquet.compactOpenContainment_of_closed_subgroup
    (isClosed_standardUnipotentPoints i ν J)
    (standardUnipotent_le_dynamicUnipotent i ν hzeta (Over.mk (𝟙 _)))
    (Langlands.BruhatTits.dynamicUnipotentCompactOpenContainment F G hG
      (CommGroupScheme.groupHom zeta ≫ i))

/-- Choose a compact open subgroup of the actual standard unipotent group
containing a given compact subset. -/
def standardUnipotentCompactOpenSubgroup
    (hG : IsConnectedReductive G)
    (hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ (C : Set (standardUnipotentPoints i ν J)), IsCompact C →
      OpenSubgroup (standardUnipotentPoints i ν J) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro C hC
  exact (standardUnipotentPoints_compactOpenContainment i ν J hG hstandard C hC).choose

/-- The chosen subgroup is compact and contains the specified compact set. -/
theorem standardUnipotentCompactOpenSubgroup_spec
    (hG : IsConnectedReductive G)
    (hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ (C : Set (standardUnipotentPoints i ν J)) (hC : IsCompact C),
      IsCompact (standardUnipotentCompactOpenSubgroup i ν J hG hstandard C hC :
        Set (standardUnipotentPoints i ν J)) ∧
      C ⊆ (standardUnipotentCompactOpenSubgroup i ν J hG hstandard C hC :
        Set (standardUnipotentPoints i ν J)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro C hC
  exact (standardUnipotentPoints_compactOpenContainment i ν J hG hstandard C hC).choose_spec

/-- The compact-subgroup limit property follows from the same local witness. -/
theorem standardUnipotentPoints_isLimitOfCompactSubgroups
    (hG : IsConnectedReductive G)
    (hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups
      (standardUnipotentPoints i ν J) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro C hC
  obtain ⟨K, hK, hCK⟩ :=
    standardUnipotentPoints_compactOpenContainment i ν J hG hstandard C hC
  exact ⟨K.toSubgroup, hK, hCK⟩

/-- Every finite subset of the actual standard unipotent group lies in a
compact open subgroup, as required by smooth coinvariant exactness. -/
theorem standardUnipotentPoints_finite_compactOpenContainment
    (hG : IsConnectedReductive G)
    (hstandard : ∃ zeta, IsStandardCocharacter i ν J zeta) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ s : Finset (standardUnipotentPoints i ν J),
      ∃ K : OpenSubgroup (standardUnipotentPoints i ν J),
        IsCompact (K : Set (standardUnipotentPoints i ν J)) ∧
          ∀ x ∈ s, x ∈ K := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro s
  obtain ⟨K, hK, hsK⟩ :=
    standardUnipotentPoints_compactOpenContainment i ν J hG hstandard
      (s : Set (standardUnipotentPoints i ν J)) s.finite_toSet.isCompact
  exact ⟨K, hK, fun x hx => hsK hx⟩

end CompactContainment

end Langlands.GroupScheme
