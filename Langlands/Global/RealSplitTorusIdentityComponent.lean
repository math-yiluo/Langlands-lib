import Langlands.Global.PositiveRealTorusEmbedding
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-! # Positive characters and the real identity component of a split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.PositiveRealTorus

section OrderedUnits

variable (A : Type u) [Field A] [LinearOrder A] [IsStrictOrderedRing A]

/-- The inclusion of positive units through the nonnegative subsemiring. -/
def positiveUnitMap : (Nonneg A)ˣ →* Aˣ :=
  Units.map (Nonneg.coeRingHom : Nonneg A →+* A).toMonoidHom

/-- Its range is exactly the existing subgroup of positive units. -/
theorem range_positiveUnitMap :
    Set.range (positiveUnitMap A) = (Units.posSubgroup A : Set Aˣ) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (Nonneg.unitsEquivPos A y).property
  · intro hx
    refine ⟨(Nonneg.unitsEquivPos A).symm ⟨x.val, hx⟩, ?_⟩
    apply Units.ext
    rfl

variable [TopologicalSpace A]

/-- The inclusion is continuous in the inherited units topologies. -/
theorem continuous_positiveUnitMap : Continuous (positiveUnitMap A) :=
  continuous_subtype_val.units_map _

variable [OrderTopology A]

/-- Positivity is open and closed within the units of an ordered field. -/
theorem isClopen_posSubgroup :
    IsClopen (Units.posSubgroup A : Set Aˣ) := by
  constructor
  · have heq : (Units.posSubgroup A : Set Aˣ)ᶜ =
        Units.val ⁻¹' Set.Iio (0 : A) := by
      ext x
      simp only [Set.mem_compl_iff, SetLike.mem_coe, Units.mem_posSubgroup,
        Set.mem_preimage, Set.mem_Iio, not_lt]
      exact le_iff_lt_or_eq.trans (or_iff_left x.ne_zero)
    rw [← isOpen_compl_iff, heq]
    exact isOpen_Iio.preimage Units.continuous_val
  · exact isOpen_Ioi.preimage Units.continuous_val

end OrderedUnits

section CompleteOrderedUnits

variable (A : Type u) [Field A] [ConditionallyCompleteLinearOrder A] [IsStrictOrderedRing A]
variable [TopologicalSpace A] [OrderTopology A] [ContinuousInv₀ A]

/-- The positive units are connected for a complete ordered coefficient field. -/
theorem isConnected_posSubgroup :
    _root_.IsConnected (Units.posSubgroup A : Set Aˣ) := by
  have : ConnectedSpace {a : A // 0 < a} :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioi (a := (0 : A)))
  have : ConnectedSpace (Nonneg A)ˣ :=
    (Nonneg.unitsHomeomorphPos A).connectedSpace_iff.mpr inferInstance
  rw [← range_positiveUnitMap]
  exact isConnected_range (continuous_positiveUnitMap A)

/-- The identity component of the units consists precisely of positive units. -/
theorem connectedComponent_one_units :
    connectedComponent (1 : Aˣ) = (Units.posSubgroup A : Set Aˣ) := by
  apply Set.Subset.antisymm
  · exact (isClopen_posSubgroup A).connectedComponent_subset (by simp)
  · exact (isConnected_posSubgroup A).subset_connectedComponent (by simp)

end CompleteOrderedUnits

section ActualPoints

variable (F : Type u) [Field F]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (A : Type u) [Field A] [LinearOrder A] [IsStrictOrderedRing A] [Algebra F A]

open Langlands.GroupScheme

/-- Actual coefficient points whose every rational character has positive value. -/
def orderedCoefficientPositiveSubgroup : Subgroup (Lie.AffinePoints T.toGrp A) :=
  ⨅ χ : characterLattice T,
    (Units.posSubgroup A).comap (characterHom F T A χ)

theorem mem_orderedCoefficientPositiveSubgroup_iff (x : Lie.AffinePoints T.toGrp A) :
    x ∈ orderedCoefficientPositiveSubgroup F T A ↔
      ∀ χ : characterLattice T, 0 < (Lie.characterValue χ x : A) := by
  simp only [orderedCoefficientPositiveSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap,
    Units.mem_posSubgroup, characterHom_apply]

variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- Every supplied splitting computes intrinsic positivity coordinate by coordinate. -/
theorem mem_orderedCoefficientPositiveSubgroup_iff_coordinates
    (x : Lie.AffinePoints T.toGrp A) :
    x ∈ orderedCoefficientPositiveSubgroup F T A ↔
      ∀ i, 0 < (coordinates F I T e A x i : A) := by
  constructor
  · intro hx i
    have h := (mem_orderedCoefficientPositiveSubgroup_iff F T A x).mp hx
      (coordinateCharacter F I T e i)
    rwa [characterValue_coordinateCharacter] at h
  · intro hx
    apply (mem_orderedCoefficientPositiveSubgroup_iff F T A x).mpr
    intro χ
    rw [characterValue_eq_prod F I T e χ]
    change (∏ i, coordinates F I T e A x i ^ characterExponents F I T e χ i) ∈
      Units.posSubgroup A
    exact (Units.posSubgroup A).prod_mem fun i _ =>
      (Units.posSubgroup A).zpow_mem (hx i) _

end ActualPoints

section CompleteActualPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable (A : Type u) [Field A] [ConditionallyCompleteLinearOrder A]
variable [IsStrictOrderedRing A] [Algebra F A]
variable [TopologicalSpace A] [OrderTopology A] [IsTopologicalRing A] [ContinuousInv₀ A]

local instance identityComponentAffinePointsTopology (G : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (Lie.AffinePoints G A) :=
  GroupScheme.affinePointsTopologicalSpace G (CommAlgCat.of F A)

include I e

/-- Intrinsic character positivity is exactly the actual real identity component. -/
theorem connectedComponent_one_eq_orderedCoefficientPositiveSubgroup :
    connectedComponent (1 : Lie.AffinePoints T.toGrp A) =
      (orderedCoefficientPositiveSubgroup F T A : Set (Lie.AffinePoints T.toGrp A)) := by
  ext x
  change x ∈ connectedComponent (1 : Lie.AffinePoints T.toGrp A) ↔
    x ∈ orderedCoefficientPositiveSubgroup F T A
  rw [mem_orderedCoefficientPositiveSubgroup_iff_coordinates F T A I e]
  constructor
  · intro hx i
    have hy := (continuous_coordinates F I T e A).mapsTo_connectedComponent
      (1 : Lie.AffinePoints T.toGrp A) hx
    rw [map_one, connectedComponent_pi] at hy
    have hi := hy i (Set.mem_univ i)
    change coordinates F I T e A x i ∈ connectedComponent (1 : Aˣ) at hi
    rw [connectedComponent_one_units] at hi
    exact hi
  · intro hx
    have hy : coordinates F I T e A x ∈ connectedComponent (1 : I → Aˣ) := by
      rw [connectedComponent_pi]
      intro i _
      change coordinates F I T e A x i ∈ connectedComponent (1 : Aˣ)
      rw [connectedComponent_one_units]
      exact hx i
    have hz := (continuous_coordinates_symm F I T e A).mapsTo_connectedComponent
      (1 : I → Aˣ) hy
    simpa using hz

/-- Characterwise description of the actual real identity component. -/
theorem mem_connectedComponent_one_iff_characters (x : Lie.AffinePoints T.toGrp A) :
    x ∈ connectedComponent (1 : Lie.AffinePoints T.toGrp A) ↔
      ∀ χ : characterLattice T, 0 < (Lie.characterValue χ x : A) := by
  rw [connectedComponent_one_eq_orderedCoefficientPositiveSubgroup F T I e A]
  exact mem_orderedCoefficientPositiveSubgroup_iff F T A x

/-- Coordinatewise description, valid also for a rank-zero supplied splitting. -/
theorem mem_connectedComponent_one_iff_coordinates (x : Lie.AffinePoints T.toGrp A) :
    x ∈ connectedComponent (1 : Lie.AffinePoints T.toGrp A) ↔
      ∀ i, 0 < (coordinates F I T e A x i : A) := by
  rw [connectedComponent_one_eq_orderedCoefficientPositiveSubgroup F T I e A]
  exact mem_orderedCoefficientPositiveSubgroup_iff_coordinates F T A I e x

/-- The intrinsically defined positive subgroup is connected. -/
theorem isConnected_orderedCoefficientPositiveSubgroup :
    _root_.IsConnected
      (orderedCoefficientPositiveSubgroup F T A : Set (Lie.AffinePoints T.toGrp A)) := by
  rw [← connectedComponent_one_eq_orderedCoefficientPositiveSubgroup F T I e A]
  exact isConnected_connectedComponent

/-- The intrinsically defined positive subgroup is closed in the actual point topology. -/
theorem isClosed_orderedCoefficientPositiveSubgroup :
    IsClosed
      (orderedCoefficientPositiveSubgroup F T A : Set (Lie.AffinePoints T.toGrp A)) := by
  rw [← connectedComponent_one_eq_orderedCoefficientPositiveSubgroup F T I e A]
  exact isClosed_connectedComponent

end CompleteActualPoints

end Langlands.Global.PositiveRealTorus
