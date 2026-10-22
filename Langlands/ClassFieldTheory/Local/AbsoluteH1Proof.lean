import Langlands.ClassFieldTheory.Local.AbsoluteH1Statement
import Langlands.ClassFieldTheory.Local.RelativeH1Proof
import Langlands.ClassFieldTheory.Local.FixedFieldUnits
import Langlands.ClassFieldTheory.Local.ClosureCoefficients
import Langlands.Cohomology.Continuous.FiniteQuotientComparisonProof

noncomputable section

open CategoryTheory
open Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u v

theorem finiteStageUnitH1_subsingleton (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (N : OpenNormalSubgroup Gal(L/K)) :
    Subsingleton (groupCohomology (finiteQuotientRep (unitsRepresentation K L) N) 1) := by
  let H : ClosedSubgroup Gal(L/K) := ⟨N.toSubgroup, N.toOpenSubgroup.isClosed⟩
  let : H.Normal := N.isNormal'
  let E := IntermediateField.fixedField H.toSubgroup
  have hopen : IsOpen E.fixingSubgroup.carrier := by
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
    exact N.toOpenSubgroup.isOpen
  let : FiniteDimensional K E := (InfiniteGalois.isOpen_iff_finite E).mp hopen
  let : Subsingleton (relativeCohomology K E 1) := finiteRelativeH1Vanishing K E
  exact (fixedFieldCohomologyIso K L H 1).toLinearEquiv.injective.subsingleton

theorem absoluteH1Vanishing : AbsoluteH1Vanishing.{u} := by
  intro K _ _
  let : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  let A : DiscreteModule IntegerScalars.{u} (Field.absoluteGaloisGroup K) :=
    { toTopRep := absoluteUnits K
      isDiscrete := inferInstance
      continuous_action := continuous_unitAction K (AlgebraicClosure K) }
  have hstage (N : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
      Subsingleton (groupCohomology (finiteQuotientRep A.toRep N) 1) :=
    finiteStageUnitH1_subsingleton K (AlgebraicClosure K) N
  have hz : Limits.IsZero (finiteQuotientCohomology A.toRep 1) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    apply Limits.colimit.hom_ext
    intro N
    let := hstage (OrderDual.ofDual N)
    exact (ModuleCat.isZero_of_subsingleton
      (groupCohomology (finiteQuotientRep A.toRep (OrderDual.ofDual N)) 1)).eq_of_src _ _
  let := ModuleCat.subsingleton_of_isZero hz
  exact (finiteQuotientComparisonLinearEquiv A 1).symm.injective.subsingleton

end Langlands.ClassFieldTheory.Local
