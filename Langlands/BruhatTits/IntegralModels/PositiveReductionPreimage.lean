import Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen
import Langlands.BruhatTits.IntegralModels.ReductionPreimage
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence

/-! # Positive-subgroup containment and reduction preimages -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

namespace SpecialFibreQuotientData

variable [IsLocalRing R]
variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)

/-- A section reducing to the identity reduces into every supplied radical. -/
theorem congruenceKernel_le_positiveSections :
    D.neutral.congruenceKernel ≤ Q.positiveSections := by
  intro x hx
  change D.neutral.reduction x ∈ Q.radicalPoints
  change D.neutral.reduction x = 1 at hx
  rw [hx]
  exact Q.radicalPoints.one_mem

/-- Containment of the target positive subgroup in the source positive subgroup
supplies the generic congruence containment needed for exact section lifting. -/
theorem congruenceSubgroup_le_integralPoints_of_positivePoints_le
    {source : RelativeComponentModelData R K G}
    (Qsource : SpecialFibreQuotientData source)
    (hpositive : Q.positivePoints ≤ Qsource.positivePoints) :
    D.neutral.congruenceSubgroup ≤ source.neutral.integralPoints :=
  Q.congruenceSubgroup_le_positivePoints.trans
    (hpositive.trans Qsource.positivePoints_le_integralPoints)

end SpecialFibreQuotientData

namespace RelativeComponentModelHom

variable [HenselianLocalRing R]
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target)

attribute [local instance] specialFibre_affine specialFibre_isAffine

/-- With rational surjectivity of the schematic-image projection, positive
subgroup containment implies the exact reduction-preimage assertion. -/
theorem hasParabolicReductionPreimage_of_positivePoints_le
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)))
    (Q : SpecialFibreQuotientData target) (Qsource : SpecialFibreQuotientData source)
    (hpositive : Q.positivePoints ≤ Qsource.positivePoints) :
    φ.HasParabolicReductionPreimage :=
  (φ.hasParabolicReductionPreimage_iff source.neutral_smooth hπ).mpr
    (φ.congruenceKernel_le_sectionRange_iff.mpr
      (Q.congruenceSubgroup_le_integralPoints_of_positivePoints_le Qsource hpositive))

/-- Over a perfect residue field one can choose actual reductive quotients,
so the universally quantified positive-radical clause suffices. -/
theorem hasParabolicReductionPreimage_of_reductivePositivePoints_le
    [PerfectField (IsLocalRing.ResidueField R)]
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)))
    (hpositive : ∀ (Q : SpecialFibreQuotientData target)
      (Qsource : SpecialFibreQuotientData source),
      Q.IsReductiveQuotient → Qsource.IsReductiveQuotient →
        Q.positivePoints ≤ Qsource.positivePoints) :
    φ.HasParabolicReductionPreimage := by
  obtain ⟨Q, hQ⟩ := SpecialFibreQuotientData.exists_isReductiveQuotient target
  obtain ⟨Qsource, hQsource⟩ :=
    SpecialFibreQuotientData.exists_isReductiveQuotient source
  exact φ.hasParabolicReductionPreimage_of_positivePoints_le hπ Q Qsource
    (hpositive Q Qsource hQ hQsource)

/-- A source section above a specified target section, with the congruence
containment supplied by positive-subgroup monotonicity. -/
def positiveReductionPreimageLift
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)))
    (Q : SpecialFibreQuotientData target) (Qsource : SpecialFibreQuotientData source)
    (hpositive : Q.positivePoints ≤ Qsource.positivePoints)
    (x : φ.specialFibreImagePoints.comap target.neutral.reduction) :
    source.neutral.integralSections :=
  φ.reductionPreimageLift source.neutral_smooth hπ
    (Q.congruenceSubgroup_le_integralPoints_of_positivePoints_le Qsource hpositive) x

/-- The chosen lift maps to the original target integral section. -/
theorem positiveReductionPreimageLift_spec
    (hπ : Function.Surjective
      (rationalPoints.map (SchematicImage.projection φ.neutralSpecialFibreMap)))
    (Q : SpecialFibreQuotientData target) (Qsource : SpecialFibreQuotientData source)
    (hpositive : Q.positivePoints ≤ Qsource.positivePoints)
    (x : φ.specialFibreImagePoints.comap target.neutral.reduction) :
    rationalPoints.map φ.neutral.hom
      (φ.positiveReductionPreimageLift hπ Q Qsource hpositive x) = x :=
  φ.reductionPreimageLift_spec source.neutral_smooth hπ
    (Q.congruenceSubgroup_le_integralPoints_of_positivePoints_le Qsource hpositive) x

end RelativeComponentModelHom

end Langlands.BruhatTits.IntegralModels
