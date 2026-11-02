import Langlands.Group.GL.ParabolicQuotientTopology
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.GeneralLinear

/-! # The identity-test GL rational-point comparison is a homeomorphism -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable (N : ℕ) (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local instance : IsAffine (groupScheme (Fin N) (CommRingCat.of R)).X.left :=
  isAffine_groupScheme (Fin N) (CommRingCat.of R)

local instance : TopologicalSpace
    (Langlands.AlgebraicGeometry.PointTopology.RationalPoint R (groupScheme (Fin N) (CommRingCat.of R)).X) :=
  Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology R (groupScheme (Fin N) (CommRingCat.of R)).X

/-- The existing identity-test and matrix-point homeomorphisms composed. -/
def rationalPointsHomeomorph :
    Langlands.AlgebraicGeometry.PointTopology.RationalPoint R (groupScheme (Fin N) (CommRingCat.of R)).X ≃ₜ
      Langlands.GeneralLinear N R :=
  (Langlands.AlgebraicGeometry.PointTopology.rationalPointHomeomorph R (groupScheme (Fin N) (CommRingCat.of R)).X).trans
    (Langlands.AlgebraicGeometry.PointTopology.GeneralLinear.schemePointHomeomorph (Fin N) R R)

omit [TopologicalSpace R] [IsTopologicalRing R] in
private theorem pointsEquiv_identityTest
    (x : Langlands.AlgebraicGeometry.PointTopology.RationalPoint R
      (groupScheme (Fin N) (CommRingCat.of R)).X) :
    pointsEquiv (Fin N) (CommRingCat.of R)
        (Langlands.AlgebraicGeometry.PointTopology.ringTest R R)
        (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv R _ x) =
      pointsEquiv (Fin N) (CommRingCat.of R)
        (Over.mk (𝟙 (Spec (CommRingCat.of R)))) x := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  erw [pointsEquiv_apply_apply]

set_option maxHeartbeats 800000 in
/-- This homeomorphism is exactly the existing algebraic rational-point map. -/
@[simp] theorem rationalPointsHomeomorph_apply
    (x : Langlands.AlgebraicGeometry.PointTopology.RationalPoint R (groupScheme (Fin N) (CommRingCat.of R)).X) :
    rationalPointsHomeomorph N R x = rationalPointsEquiv N (CommRingCat.of R) x := by
  let y := Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv R (groupScheme (Fin N) (CommRingCat.of R)).X x
  have hp := pointsEquiv_identityTest N R x
  have h := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor (Fin N) (CommRingCat.of R)) (corepresentableBy (Fin N) (CommRingCat.of R))
      (CommAlgCat.of R R) y
  erw [functor_map_apply, Corepresented.affineSectionsIso_hom_ringHom] at h
  change Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (pointsEquiv (Fin N) (CommRingCat.of R)
        ((algSpec (CommRingCat.of R)).obj (Opposite.op (CommAlgCat.of R R))) y) =
    affinePointsEquiv (Fin N) (CommRingCat.of R) (CommAlgCat.of R R) y at h
  erw [hp] at h
  change Langlands.AlgebraicGeometry.PointTopology.GeneralLinear.schemePointHomeomorph (Fin N) R R y = _
  rw [Langlands.AlgebraicGeometry.PointTopology.GeneralLinear.schemePointHomeomorph_apply]
  exact h.symm


/-- The same algebraic rational-point equivalence, with continuity in both directions. -/
def rationalPointsContinuousMulEquiv :
    Langlands.AlgebraicGeometry.PointTopology.RationalPoint R
      (groupScheme (Fin N) (CommRingCat.of R)).X ≃ₜ* Langlands.GeneralLinear N R where
  toMulEquiv := rationalPointsEquiv N (CommRingCat.of R)
  continuous_toFun :=
    (rationalPointsHomeomorph N R).continuous_toFun.congr
      (rationalPointsHomeomorph_apply N R)
  continuous_invFun := by
    have he : (rationalPointsHomeomorph N R).toEquiv =
        (rationalPointsEquiv N (CommRingCat.of R)).toEquiv :=
      Equiv.ext (rationalPointsHomeomorph_apply N R)
    change Continuous (rationalPointsEquiv N (CommRingCat.of R)).toEquiv.symm
    rw [← he]
    exact (rationalPointsHomeomorph N R).continuous_invFun

@[simp] theorem rationalPointsContinuousMulEquiv_apply
    (x : Langlands.AlgebraicGeometry.PointTopology.RationalPoint R
      (groupScheme (Fin N) (CommRingCat.of R)).X) :
    rationalPointsContinuousMulEquiv N R x = rationalPointsEquiv N (CommRingCat.of R) x := rfl

/-- The evaluation topology on the identity-test carrier is a topological group topology. -/
theorem rationalPoints_isTopologicalGroup :
    IsTopologicalGroup (Langlands.AlgebraicGeometry.PointTopology.RationalPoint R
      (groupScheme (Fin N) (CommRingCat.of R)).X) :=
  (rationalPointsContinuousMulEquiv N R).toHomeomorph.isInducing.isTopologicalGroup
    (rationalPointsEquiv N (CommRingCat.of R))

variable {N} (B : Langlands.GeneralLinear.BlockShape N)

/-- The algebraic parabolic comparison preserves precisely the induced subgroup topologies. -/
def rationalParabolicContinuousMulEquiv :
    (Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≃ₜ* B.parabolic R where
  toMulEquiv := rationalParabolicEquiv B
  continuous_toFun :=
    ((rationalPointsContinuousMulEquiv N R).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((rationalPointsContinuousMulEquiv N R).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The algebraic Levi comparison preserves precisely the induced subgroup topologies. -/
def rationalLeviContinuousMulEquiv :
    (Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≃ₜ* B.leviSubgroup R where
  toMulEquiv := rationalLeviEquiv B
  continuous_toFun :=
    ((rationalPointsContinuousMulEquiv N R).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((rationalPointsContinuousMulEquiv N R).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The algebraic unipotent comparison preserves precisely the induced subgroup topologies. -/
def rationalUnipotentContinuousMulEquiv :
    (Dynamic.unipotent (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≃ₜ* B.unipotentSubgroup R where
  toMulEquiv := rationalUnipotentEquiv B
  continuous_toFun :=
    ((rationalPointsContinuousMulEquiv N R).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((rationalPointsContinuousMulEquiv N R).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The algebraic Levi points also identify with the existing product of general linear groups. -/
def rationalLeviProductContinuousMulEquiv :
    (Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≃ₜ* B.Levi R :=
  (rationalLeviContinuousMulEquiv R B).trans (B.leviEquivContinuous R).symm

/-- The actual dynamic limit map is continuous for these subgroup topologies. -/
def rationalLimitContinuousHom :
    ContinuousMonoidHom
      ((Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
      ((Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of R))))) where
  toMonoidHom := Dynamic.limitHom (blockShapeCocharacter B (CommRingCat.of R)) _
  continuous_toFun := by
    have h := (rationalLeviContinuousMulEquiv R B).symm.continuous.comp
      ((B.leviEquivContinuous R).continuous.comp
        ((B.leviProjectionContinuous R).continuous.comp
          (rationalParabolicContinuousMulEquiv R B).continuous))
    apply h.congr
    intro g
    apply (rationalLeviEquiv (R := CommRingCat.of R) B).injective
    change rationalLeviEquiv B ((rationalLeviEquiv B).symm _) =
      rationalLeviEquiv B (Dynamic.limitHom (blockShapeCocharacter B (CommRingCat.of R)) _ g)
    rw [MulEquiv.apply_symm_apply, rationalLeviEquiv_limitHom]
    rfl

/-- Under the continuous comparisons, the dynamic limit is exactly the block projection. -/
@[simp] theorem rationalLeviProductContinuousMulEquiv_limit
    (g : (Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    rationalLeviProductContinuousMulEquiv R B (rationalLimitContinuousHom R B g) =
      B.leviProjection R (rationalParabolicContinuousMulEquiv R B g) := by
  change (B.leviEquiv R).symm (rationalLeviEquiv (R := CommRingCat.of R) B _) = _
  change (B.leviEquiv R).symm
    (rationalLeviEquiv (R := CommRingCat.of R) B
      (Dynamic.limitHom (blockShapeCocharacter B (CommRingCat.of R)) _ g)) = _
  rw [rationalLeviEquiv_limitHom, MulEquiv.symm_apply_apply]
  rfl

/-- The actual inclusion of the dynamic Levi points in the dynamic parabolic is continuous. -/
def rationalLeviInclusionContinuousHom :
    ContinuousMonoidHom
      ((Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
      ((Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of R))))) where
  toMonoidHom := Subgroup.inclusion (Dynamic.centralizer_le_parabolic _ _)
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The continuous inclusion is exactly the existing matrix Levi inclusion. -/
@[simp] theorem rationalParabolicContinuousMulEquiv_inclusion
    (z : (Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    rationalParabolicContinuousMulEquiv R B (rationalLeviInclusionContinuousHom R B z) =
      B.leviAsParabolic R (rationalLeviContinuousMulEquiv R B z) :=
  rationalParabolicEquiv_inclusion B z

/-- The rational-point comparison preserves the actual Levi conjugation action on U. -/
theorem rationalUnipotentContinuousMulEquiv_conj
    (z : (Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (u : (Dynamic.unipotent (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    (rationalUnipotentContinuousMulEquiv R B
      (Dynamic.centralizerConj (blockShapeCocharacter B (CommRingCat.of R)) _ z u) :
        Langlands.GeneralLinear N R) =
      (rationalLeviContinuousMulEquiv R B z : Langlands.GeneralLinear N R) *
        (rationalUnipotentContinuousMulEquiv R B u : Langlands.GeneralLinear N R) *
        (rationalLeviContinuousMulEquiv R B z : Langlands.GeneralLinear N R)⁻¹ := by
  change rationalPointsEquiv N (CommRingCat.of R) (_ * _ * _⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- The actual dynamic unipotent points, regarded as a subgroup of the parabolic points. -/
abbrev rationalUnipotentInParabolic :
    Subgroup ((Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :=
  ((Dynamic.unipotent (blockShapeCocharacter B (CommRingCat.of R))).carrier
    (Over.mk (𝟙 (Spec (CommRingCat.of R))))).subgroupOf
      ((Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of R)))))

instance rationalUnipotentInParabolic_normal :
    (rationalUnipotentInParabolic R B).Normal :=
  Dynamic.unipotent_subgroupOf_parabolic_normal _ _

/-- The denominator of the quotient is exactly the kernel of the actual dynamic limit. -/
theorem rationalLimitContinuousHom_ker :
    (rationalLimitContinuousHom R B).toMonoidHom.ker =
      rationalUnipotentInParabolic R B :=
  Dynamic.ker_limitHom _ _

/-- The actual dynamic parabolic quotient, with its quotient topology, is the dynamic Levi. -/
def rationalParabolicQuotientLeviContinuousMulEquiv :
    ((Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) ⧸ rationalUnipotentInParabolic R B ≃ₜ*
      ((Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of R))))) where
  toMulEquiv :=
    (QuotientGroup.quotientMulEquivOfEq (Dynamic.ker_limitHom
      (blockShapeCocharacter B (CommRingCat.of R)) _).symm).trans
      (QuotientGroup.quotientKerEquivOfRightInverse
        (Dynamic.limitHom (blockShapeCocharacter B (CommRingCat.of R)) _)
        (Subgroup.inclusion (Dynamic.centralizer_le_parabolic _ _))
        (Dynamic.limitHom_inclusion _ _))
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (rationalUnipotentInParabolic R B)).continuous_iff.mpr
      (rationalLimitContinuousHom R B).continuous
  continuous_invFun :=
    QuotientGroup.continuous_mk.comp (rationalLeviInclusionContinuousHom R B).continuous

@[simp] theorem rationalParabolicQuotientLeviContinuousMulEquiv_mk
    (g : (Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    rationalParabolicQuotientLeviContinuousMulEquiv R B (QuotientGroup.mk g) =
      rationalLimitContinuousHom R B g := rfl

@[simp] theorem rationalParabolicQuotientLeviContinuousMulEquiv_symm_apply
    (z : (Dynamic.centralizer (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    (rationalParabolicQuotientLeviContinuousMulEquiv R B).symm z =
      QuotientGroup.mk (rationalLeviInclusionContinuousHom R B z) := rfl

/-- The same quotient identifies continuously with the existing product Levi. -/
def rationalParabolicQuotientProductLeviContinuousMulEquiv :
    ((Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) ⧸ rationalUnipotentInParabolic R B ≃ₜ*
      B.Levi R :=
  (rationalParabolicQuotientLeviContinuousMulEquiv R B).trans
    (rationalLeviProductContinuousMulEquiv R B)

@[simp] theorem rationalParabolicQuotientProductLeviContinuousMulEquiv_mk
    (g : (Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    rationalParabolicQuotientProductLeviContinuousMulEquiv R B (QuotientGroup.mk g) =
      B.leviProjection R (rationalParabolicContinuousMulEquiv R B g) :=
  rationalLeviProductContinuousMulEquiv_limit R B g

/-- The dynamic quotient also identifies continuously with the existing matrix quotient. -/
def rationalParabolicQuotientMatrixContinuousMulEquiv :
    ((Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) ⧸ rationalUnipotentInParabolic R B ≃ₜ*
      B.parabolic R ⧸ B.unipotentRadical R :=
  (rationalParabolicQuotientProductLeviContinuousMulEquiv R B).trans
    (B.parabolicQuotientLeviContinuous R).symm

@[simp] theorem rationalParabolicQuotientMatrixContinuousMulEquiv_mk
    (g : (Dynamic.parabolic (blockShapeCocharacter B (CommRingCat.of R))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :
    rationalParabolicQuotientMatrixContinuousMulEquiv R B (QuotientGroup.mk g) =
      QuotientGroup.mk (rationalParabolicContinuousMulEquiv R B g) := by
  apply (B.parabolicQuotientLeviContinuous R).injective
  change (B.parabolicQuotientLevi R) ((B.parabolicQuotientLevi R).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact rationalParabolicQuotientProductLeviContinuousMulEquiv_mk R B g

end Langlands.GroupScheme.GeneralLinear
