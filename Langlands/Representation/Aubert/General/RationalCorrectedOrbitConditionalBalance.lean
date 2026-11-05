import Langlands.Representation.Aubert.General.RationalCorrectedOrbitBalanceModels
import Langlands.Representation.Aubert.General.EqualCentralizerHaarBalance

/-! # Conditional character detection for the actual corrected orbit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

namespace CorrectedOrbitCocharacterRealization

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} {I K : Finset (SimpleRoot i ν)}
    {m : rationalPoints G} (r : CorrectedOrbitCocharacterRealization i ν I K m)

local instance correctedOrbitConditionalBalanceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance correctedOrbitConditionalBalanceActingAffineHom :
    IsAffineHom r.actingScheme.X.hom :=
  (Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom r.zeta ≫ i)).isAffineHom

local instance correctedOrbitConditionalBalanceActingAffine :
    IsAffine r.actingScheme.X.left :=
  isAffine_of_isAffineHom r.actingScheme.X.hom

section Determinants

variable [LocallyOfFiniteType G.X.hom]

/-- The actual common-Levi determinant discrepancy, using the two represented
full radicals, their literal intersection, and their canonical Lie coordinates. -/
def determinantSquareDefect : rationalCharacters r.actingScheme :=
  Dynamic.centralizingDeterminantSquareDefect r.zeta r.eta r.actingHom
    r.acting_range_left r.acting_range_right r.leftRadical_represented
    r.rightRadical_represented r.intersection_represented
    r.leftRadicalCoordinates r.rightRadicalCoordinates r.intersectionCoordinates

variable [Mono i.hom.hom.left] (hroot : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp)

include hroot hT

/-- The actual determinant discrepancy vanishes after restriction to the
original split torus. This statement needs no character-detection premise. -/
theorem characterRestrict_determinantSquareDefect_eq_zero :
    characterRestrict r.torusHom r.determinantSquareDefect = 0 :=
  Dynamic.characterRestrict_centralizingDeterminantSquareDefect_eq_zero
    hroot hT r.zeta r.eta r.centralizer_eq r.actingHom
    r.acting_range_left r.acting_range_right r.leftRadical_represented
    r.rightRadical_represented r.intersection_represented
    r.torusHom r.torusHom_comp
    r.leftRadicalCoordinates r.rightRadicalCoordinates r.intersectionCoordinates

/-- Injectivity of restriction to the original torus would force the actual
common-Levi determinant discrepancy to vanish. The premise remains explicit. -/
theorem determinantSquareDefect_eq_zero_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict r.torusHom)) :
    r.determinantSquareDefect = 0 := by
  apply hinj
  rw [r.characterRestrict_determinantSquareDefect_eq_zero hroot hT, map_zero]

end Determinants

section Haar

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Smooth G.X.hom] [Mono i.hom.hom.left]
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)

include hroot hT

local instance correctedOrbitConditionalBalanceTopology :
    TopologicalSpace (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X) :=
  pointTopology

variable [LocallyCompactSpace
    (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X)]
    [NonarchimedeanGroup
      (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X)]
    [T2Space (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X)]
    (hUI : IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (hUK : IsClosed (unipotent i ν K : Set (rationalPoints G)))
    (hdI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (hdK : IsSemidirectDecomposition (parabolic i ν K) (levi i ν K) (unipotent i ν K))
    (hK : ∀ x : rationalPoints G, x ∈ levi i ν I ↔ m⁻¹ * x * m ∈ levi i ν K)

/-- Character detection on the represented common Levi gives the exact
literal squared-modulus identity at every original Levi point. -/
theorem squared_modulus_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict r.torusHom))
    (l : levi i ν I) :
    (HaarModulus.closedRestrictCharacter (unipotent i ν I) hUI (levi i ν I)
        hdI.levi_le_normalizer l : ℝ≥0) *
      (HaarModulus.closedRestrictCharacter (unipotent i ν K) hUK (levi i ν K)
        hdK.levi_le_normalizer (conjugationEquiv m hK l) : ℝ≥0) =
      (HaarModulus.closedRestrictCharacter
        (CorrectedFiltration.orbitUnipotentIntersection (unipotent i ν I) (unipotent i ν K) m)
        (CorrectedFiltration.isClosed_orbitUnipotentIntersection hUI hUK m) (levi i ν I)
        (CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection hdI hdK m hK)
        l : ℝ≥0) ^ 2 := by
  apply r.squared_modulus_of_dynamic_balance hUI hUK hdI hdK hK
  intro z
  exact centralizingHaarCharacter_values_square_of_centralizer_eq
    hroot hT r.zeta r.eta r.centralizer_eq r.actingHom
    r.acting_range_left r.acting_range_right r.leftRadical_represented
    r.rightRadical_represented r.intersection_represented
    r.torusHom r.torusHom_comp
    r.leftRadicalCoordinates r.rightRadicalCoordinates r.intersectionCoordinates
    (r.isClosed_left hUI) (r.isClosed_right hUK) (r.isClosed_intersection hUI hUK) hinj z

end Haar

end CorrectedOrbitCocharacterRealization

end Langlands.Aubert.General.RationalPointFamily
