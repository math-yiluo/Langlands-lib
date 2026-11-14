import Langlands.Geometry.Building.AlgebraicRankOneCoordinates
import Langlands.Geometry.Building.CentralizerCoordinateCompatibility

/-! # Coroot character values forced by coherent rank-one coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S Z : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : Z.toGrp ⟶ G} {s : S.toGrp ⟶ Z.toGrp}
  {b : characterLattice S}

namespace AlgebraicSL2RootCoordinates

variable (C : AlgebraicSL2RootCoordinates i j s b)

/-- The centralizer point induced by a unit through the actual coroot morphism. -/
def corootPoint : C.extensionˣ →* rationalPoints Z.toGrp :=
  (rationalPoints.map C.coroot).comp
    (WeilGm.rationalUnitsEquiv k C.extension).symm.toMonoidHom

theorem map_corootPoint (t : C.extensionˣ) :
    rationalPoints.map j (C.corootPoint t) =
      C.rho (SpecialLinear.Root.contractingMatrix (by decide : (0 : Fin 2) ≠ 1) t) :=
  C.coroot_points t

/-- The positive root character on the coroot is the square character. -/
theorem character_corootPoint (t : C.extensionˣ) :
    rationalCharacterEval C.positive.character
        (GaloisPointComparison.rationalExtend k C.extension Z.toGrp (C.corootPoint t)) =
      t ^ 2 := by
  have hc := C.positive.conjugation (C.corootPoint t) (1 : C.extension)
  rw [C.map_corootPoint] at hc
  have hr := congrArg C.rho
    (SpecialLinear.Root.contractingMatrix_conjugate
      (by decide : (0 : Fin 2) ≠ 1) t (1 : C.extension))
  simp only [map_mul, map_inv, C.rho_upper] at hr
  have he := C.positive.equiv.injective (Subtype.ext (hc.symm.trans hr))
  apply Units.ext
  simpa using congrArg Multiplicative.toAdd he

/-- A norm-calibrated extension valuation computes the root pairing on a coroot. -/
theorem eval_corootPoint [IsAffine S.toGrp.X.left] [IsAffine Z.toGrp.X.left]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w) (t : C.extensionˣ) :
    ((eval S b (IntegerValuation.centralizerValuation v s h (C.corootPoint t)).toAdd :
      ℝ) : WithTop ℝ) = 2 • w (t : C.extension) := by
  have hc := hw.apply_rationalCharacterEval C.positive.character (C.corootPoint t)
  rw [IntegerValuation.characterNormOrder_eq_eval v s h C.positive.restriction,
    C.character_corootPoint] at hc
  simpa only [Units.val_pow_eq_pow_val, AddValuation.map_pow] using hc.symm

end AlgebraicSL2RootCoordinates

namespace AlgebraicSU3RootCoordinates

variable (C : AlgebraicSU3RootCoordinates i j s b)

/-- The centralizer point induced by a unit through the unitary coroot morphism. -/
def corootPoint : C.extensionˣ →* rationalPoints Z.toGrp :=
  (rationalPoints.map C.coroot).comp
    (WeilGm.rationalUnitsEquiv k C.extension).symm.toMonoidHom

theorem map_corootPoint (t : C.extensionˣ) :
    rationalPoints.map j (C.corootPoint t) =
      C.rho ⟨SU3Root.diagonal (SU3Root.fieldInvolution C.base C.extension) t,
        SU3Root.diagonal_mem_specialUnitarySubgroup
          (SU3Root.fieldInvolution C.base C.extension) t⟩ :=
  C.coroot_points t

/-- The positive unitary root character equals the actual diagonal root scalar. -/
theorem character_corootPoint (t : C.extensionˣ) :
    rationalCharacterEval C.positive.character
        (GaloisPointComparison.rationalExtend k C.extension Z.toGrp (C.corootPoint t)) =
      SU3Root.diagonalRootScalar (SU3Root.fieldInvolution C.base C.extension) t := by
  let c := SU3Root.fieldInvolution C.base C.extension
  let p := SU3Root.rationalLift C.base C.extension (1 : C.extension)
  let d : SU3Root.specialUnitarySubgroup c :=
    ⟨SU3Root.diagonal c t, SU3Root.diagonal_mem_specialUnitarySubgroup c t⟩
  have hm : d * ⟨SU3Root.Parameters.embedding c p,
        SU3Root.embedding_mem_specialUnitarySubgroup c p⟩ * d⁻¹ =
      (⟨SU3Root.Parameters.embedding c
          (SU3Root.Parameters.scale (SU3Root.diagonalRootScalar c t : C.extension) p),
        SU3Root.embedding_mem_specialUnitarySubgroup c _⟩ :
          SU3Root.specialUnitarySubgroup c) :=
    Subtype.ext (SU3Root.diagonal_conjugate_embedding c t p)
  have hr := congrArg C.rho hm
  dsimp only [c, d] at hr
  simp only [map_mul, map_inv, C.rho_upper] at hr
  have hc := C.positive.conjugation (C.corootPoint t) p
  rw [C.map_corootPoint] at hc
  have he := C.positive.equiv.injective (Subtype.ext (hc.symm.trans hr))
  apply Units.ext
  simpa only [p, SU3Root.Parameters.first_scale, SU3Root.rationalLift_first, mul_one]
    using congrArg SU3Root.Parameters.first he

/-- Under conjugation invariance and norm calibration, the root pairing is the unit value. -/
theorem eval_corootPoint [IsAffine S.toGrp.X.left] [IsAffine Z.toGrp.X.left]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w)
    (hbar : ∀ x, w ((SU3Root.fieldInvolution C.base C.extension).bar x) = w x)
    (t : C.extensionˣ) :
    ((eval S b (IntegerValuation.centralizerValuation v s h (C.corootPoint t)).toAdd :
      ℝ) : WithTop ℝ) = w (t : C.extension) := by
  have hc := hw.apply_rationalCharacterEval C.positive.character (C.corootPoint t)
  rw [IntegerValuation.characterNormOrder_eq_eval v s h C.positive.restriction,
    C.character_corootPoint, SU3Root.diagonalRootScalar_value w hbar] at hc
  exact hc.symm

end AlgebraicSU3RootCoordinates

end Langlands.Geometry.Building
