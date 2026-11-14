import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.Reductive.ParabolicUnipotentKernel

/-! # Radical preimages and integral points of incident models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)
  (Q : SpecialFibreQuotientData target)

namespace RelativeComponentModelHom

/-- An exact reduction-preimage equality transfers any subgroup of the
special-fibre image to integral points of the source model. -/
theorem positivePoints_le_source_of_radicalPoints_le
    (hpre : φ.HasParabolicReductionPreimage)
    (hrad : Q.radicalPoints ≤ φ.specialFibreImagePoints) :
    Q.positivePoints ≤ source.neutral.integralPoints := by
  rintro g ⟨x, hx, rfl⟩
  have himage : x ∈ (rationalPoints.map φ.neutral.hom).range := by
    rw [← hpre]
    exact hrad hx
  obtain ⟨y, rfl⟩ := himage
  exact ⟨y, (φ.neutral_integralPointMap y).symm⟩

/-- The actual residue-field radical lies in the actual parabolic schematic
image. No surjectivity on residue-field points of the model map is used. -/
theorem radicalPoints_le_specialFibreImagePoints
    (hpar : φ.HasParabolicSpecialFibreImage)
    (hrad : IsUnipotentRadical Q.radicalInclusion) :
    Q.radicalPoints ≤ φ.specialFibreImagePoints := by
  let : Smooth target.neutral.group.X.hom := target.neutral_smooth
  let : Smooth target.neutral.specialFibre.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd target.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  let : IsAffineHom target.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd target.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  let : ConnectedSpace target.neutral.specialFibre.X.left :=
    target.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres
      target.neutral_connectedFibres
  let j := hpar.radicalFactor φ.specialFibreImageInclusion Q.radicalInclusion hrad
  have hj : j ≫ φ.specialFibreImageInclusion = Q.radicalInclusion :=
    hpar.radicalFactor_comp φ.specialFibreImageInclusion Q.radicalInclusion hrad
  rintro _ ⟨x, rfl⟩
  refine ⟨rationalPoints.map j x, ?_⟩
  simp only [rationalPoints.map_apply, Category.assoc,
    ← Grp.comp_hom_hom, hj]

/-- The radical-reduction preimage for a target model lies in the neutral
integral points of an incident source whenever the parabolic image and exact
reduction-preimage clauses hold. -/
theorem positivePoints_le_source_of_parabolicReductionPreimage
    (hpar : φ.HasParabolicSpecialFibreImage)
    (hpre : φ.HasParabolicReductionPreimage)
    (hrad : IsUnipotentRadical Q.radicalInclusion) :
    Q.positivePoints ≤ source.neutral.integralPoints :=
  φ.positivePoints_le_source_of_radicalPoints_le Q hpre
    (φ.radicalPoints_le_specialFibreImagePoints Q hpar hrad)

end RelativeComponentModelHom

/-- The algebraic radical-transfer consequence of the parabolic-image and
exact reduction-preimage clauses, for actual supplied integral models. -/
def ParabolicRadicalPreimageTransferStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (source target : RelativeComponentModelData R K G)
    (φ : RelativeComponentModelHom source target)
    (Q : SpecialFibreQuotientData target),
    φ.HasParabolicSpecialFibreImage →
    φ.HasParabolicReductionPreimage →
    IsUnipotentRadical Q.radicalInclusion →
      Q.positivePoints ≤ source.neutral.integralPoints

/-- Exact integral transfer of the actual radical-reduction preimage. -/
theorem parabolicRadicalPreimageTransfer :
    ParabolicRadicalPreimageTransferStatement.{u} := by
  intro R K _ _ _ _ _ _ G source target φ Q hpar hpre hrad
  exact φ.positivePoints_le_source_of_parabolicReductionPreimage Q hpar hpre hrad

end Langlands.BruhatTits.IntegralModels
