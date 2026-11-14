import Langlands.Geometry.Building.RankOneCorootGeometricCongruence
import Langlands.GroupScheme.Torus.WeilRestrictionInduced
import Langlands.Geometry.Building.PositiveRootConeDepth
import Langlands.Geometry.Building.IntegerRootReflections

/-! # Reduction of the local coroot component to coherent rank-one coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- The complete local coroot conclusion at one character, including the affine
induced source torus and its morphism. -/
def InducedCorootComponentProperty (a : characterLattice B.S) : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (_ : IsAffine T.X.left), IsTorus T.toGrp ∧ IsInducedTorus T ∧
    ∃ f : T ⟶ B.centralizerTorus hZ, CorootComponentCongruenceProperty B hZ a T f

variable {B hZ} {b : characterLattice B.S}

namespace ValuedSL2RootCoordinates

variable (C : ValuedSL2RootCoordinates B hZ b)

include C in
theorem inducedCorootComponentProperty (hb : b ≠ 0) :
    InducedCorootComponentProperty B hZ b := by
  refine ⟨WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension,
    ?_, WeilGm.isTorus_of_finite_separable (UnramifiedClosure F) C.extension,
    WeilGm.isInducedTorus_of_finite_separable (UnramifiedClosure F) C.extension,
    C.corootMorphism, C.corootComponentCongruenceProperty hb⟩
  change IsAffine (Spec _)
  infer_instance

end ValuedSL2RootCoordinates

namespace ValuedSU3RootCoordinates

variable (C : ValuedSU3RootCoordinates B hZ b)

include C in
theorem inducedCorootComponentProperty (hb : b ≠ 0) :
    InducedCorootComponentProperty B hZ b := by
  refine ⟨WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension,
    ?_, WeilGm.isTorus_of_finite_separable (UnramifiedClosure F) C.extension,
    WeilGm.isInducedTorus_of_finite_separable (UnramifiedClosure F) C.extension,
    C.corootMorphism, C.corootComponentCongruenceProperty hb⟩
  change IsAffine (Spec _)
  infer_instance

include C in
theorem double_inducedCorootComponentProperty (hb : b ≠ 0) :
    InducedCorootComponentProperty B hZ (2 • b) := by
  refine ⟨WeilGm.commGroupScheme (CommRingCat.of (UnramifiedClosure F)) C.extension,
    ?_, WeilGm.isTorus_of_finite_separable (UnramifiedClosure F) C.extension,
    WeilGm.isInducedTorus_of_finite_separable (UnramifiedClosure F) C.extension,
    C.corootMorphism, C.double_corootComponentCongruenceProperty hb⟩
  change IsAffine (Spec _)
  infer_instance

end ValuedSU3RootCoordinates

/-- Supplied coherent coordinates for indivisible roots suffice for the complete
local coroot conclusion at every actual relative root. -/
theorem inducedCorootComponentProperty_of_valuedRankOneCoordinates
    (hcoords : ∀ b : characterLattice B.S,
      b ∈ RelativeRoot.indivisibleRoots B.i →
        (2 • b ∉ relativeRoots B.i → Nonempty (ValuedSL2RootCoordinates B hZ b)) ∧
        (2 • b ∈ relativeRoots B.i → Nonempty (ValuedSU3RootCoordinates B hZ b)))
    (a : relativeRoots B.i) :
    InducedCorootComponentProperty B hZ a.val := by
  let : Smooth H.X.hom := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos a.property.1
  have hpos : a.val ∈ positiveRelativeRoots B.i ν :=
    ⟨a.property, by rw [hν]; exact_mod_cast hD⟩
  obtain ⟨b, hb, ha⟩ :=
    B.hasOppositeFactorPairs.exists_indivisiblePositiveRoot_eq_or_double B.i hS ν hpos
  have hb0 : b ≠ 0 := hb.1.1.1
  by_cases hdbl : 2 • b ∈ relativeRoots B.i
  · obtain ⟨C⟩ := (hcoords b hb.1).2 hdbl
    rcases ha with ha | ha
    · rw [ha]
      exact C.inducedCorootComponentProperty hb0
    · rw [ha]
      exact C.double_inducedCorootComponentProperty hb0
  · obtain ⟨C⟩ := (hcoords b hb.1).1 hdbl
    rcases ha with ha | ha
    · rw [ha]
      exact C.inducedCorootComponentProperty hb0
    · exact (hdbl (ha ▸ a.property)).elim

end Langlands.Geometry.Building
