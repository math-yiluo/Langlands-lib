import Langlands.Representation.Geometric.RepresentedGeometricLemmaIntersectionPoints
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions

/-! # Levi projections on the target geometric-lemma intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

/-- The target intersection embeds in the compact-induction stabilizer. -/
def targetParabolicPointsToStabilizer
    (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) :
    ↥(pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) →*
      Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹ where
  toFun x := ⟨⟨x, pointImage_comp_le q lQ x.property.1⟩, by
    have hx := Subgroup.mem_map_equiv.mp x.property.2
    simp only [Geometric.orbitStabilizer, Subgroup.mem_comap,
      MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    simpa only [MulAut.conj_symm_apply, inv_inv] using hx⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

@[simp]
theorem targetParabolicPointsToStabilizer_apply_coe
    (x : ↥(pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom)) :
    ((D.targetParabolicPointsToStabilizer x : pointImage q) : rationalPoints G) = x := rfl

/-- Conjugation carries the target intersection parabolic into the source parabolic. -/
def targetParabolicPointsToSource :
    ↥(pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) →*
      pointImage p :=
  (Geometric.stabilizerToInducing (pointImage p) (pointImage q) z⁻¹).comp
    D.targetParabolicPointsToStabilizer

@[simp]
theorem targetParabolicPointsToSource_apply_coe
    (x : ↥(pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom)) :
    (D.targetParabolicPointsToSource x : rationalPoints G) = z * (x : rationalPoints G) * z⁻¹ := by
  rw [targetParabolicPointsToSource, MonoidHom.comp_apply,
    Geometric.stabilizerToInducing_apply, D.targetParabolicPointsToStabilizer_apply_coe, inv_inv]

/-- Conjugation carries the common target Levi into the original source Levi. -/
def targetLeviPointsToSourceLevi
    (_D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z) :
    ↥(pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom) →*
      pointImage (l ≫ p) where
  toFun x := ⟨(MulAut.conj z) x, by
    have hx := Subgroup.mem_map_equiv.mp x.property.2
    simpa only [MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv] using hx⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (MulAut.conj z)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (MulAut.conj z) (x : rationalPoints G) (y : rationalPoints G)

@[simp]
theorem targetLeviPointsToSourceLevi_apply_coe
    (x : ↥(pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom)) :
    (D.targetLeviPointsToSourceLevi x : rationalPoints G) = z * (x : rationalPoints G) * z⁻¹ := rfl

/-- Source projection of the conjugated target intersection. -/
def targetParabolicPointsToSourceLevi :
    ↥(pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) →*
      pointImage (l ≫ p) :=
  (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul).projection.comp
    D.targetParabolicPointsToSource

/-- The original and intersection Levi projections commute with conjugation. -/
theorem targetParabolicPointsToSourceLevi_eq
    (x : ↥(pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom)) :
    D.targetParabolicPointsToSourceLevi x =
      D.targetLeviPointsToSourceLevi (D.targetPoints_isSemidirectDecomposition.projection x) := by
  apply (isSemidirectDecomposition_pointImage p l r
    hp.isClosedSubgroup hr hmul).projection_eq_iff _ _ |>.mpr
  rw [D.targetLeviPointsToSourceLevi_apply_coe, D.targetParabolicPointsToSource_apply_coe]
  have hx := Subgroup.mem_map_equiv.mp
    (D.targetPoints_isSemidirectDecomposition.projection_inv_mul_mem x).2
  simpa only [MulAut.conj_symm_apply, inv_inv, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left] using hx

/-- The restricted source projection kills exactly the target intersection radical. -/
theorem targetParabolicPointsToSourceLevi_ker :
    D.targetParabolicPointsToSourceLevi.ker =
      (pointImage (lQ ≫ q) ⊓
        (pointImage (r ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom).subgroupOf
        (pointImage (lQ ≫ q) ⊓ (pointImage p).map (MulAut.conj z⁻¹).toMonoidHom) := by
  have hinj : Function.Injective D.targetLeviPointsToSourceLevi := by
    intro a b hab
    apply Subtype.ext
    apply (MulAut.conj z).injective
    exact congrArg Subtype.val hab
  ext x
  change D.targetParabolicPointsToSourceLevi x = 1 ↔ _
  rw [D.targetParabolicPointsToSourceLevi_eq,
    ← map_one D.targetLeviPointsToSourceLevi, hinj.eq_iff,
    D.targetPoints_isSemidirectDecomposition.projection_eq_one_iff]
  rfl

section Topology

variable [IsAffineHom G.X.hom]

local instance leviProjectionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

open Langlands.AlgebraicGeometry.PointTopology

/-- The section of the orbit stabilizer is continuous in the canonical point topology. -/
theorem continuous_targetParabolicPointsToStabilizer :
    Continuous D.targetParabolicPointsToStabilizer :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [IsTopologicalGroup (rationalPoints G)]

/-- The map into the source parabolic is continuous. -/
theorem continuous_targetParabolicPointsToSource :
    Continuous D.targetParabolicPointsToSource := by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, D.targetParabolicPointsToSource_apply_coe]
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

/-- The conjugation map into the original source Levi is continuous. -/
theorem continuous_targetLeviPointsToSourceLevi :
    Continuous D.targetLeviPointsToSourceLevi := by
  apply continuous_induced_rng.mpr
  simp only [Function.comp_def, D.targetLeviPointsToSourceLevi_apply_coe]
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

omit [IsTopologicalGroup (rationalPoints G)] in
/-- The literal conjugation agrees with the datum's actual represented Levi map. -/
theorem targetLeviPointsToSourceLevi_eq_intersectionConjugation
    (x : ↥(pointImage (lQ ≫ q) ⊓ (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom)) :
    D.targetLeviPointsToSourceLevi x =
      Subgroup.inclusion inf_le_left (D.intersectionLeviPointsConjugation x) := by
  apply Subtype.ext
  exact (D.intersectionLeviPointsConjugation_apply_coe x).symm

end Topology

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
