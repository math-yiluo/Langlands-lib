import Langlands.Representation.Exponents.LeviSecondAdjointnessContragredientEquivalenceStatement
import Langlands.Representation.Exponents.LeviSecondAdjointnessStructure
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactProof
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # The pointwise VI.9.6 equivalence from uniform compression stabilization -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Internal reduction of the exact pointwise equivalence to VI.9.1 uniform
compression stabilization, retaining independent field and carrier universes. -/
def LeviSecondAdjointnessContragredientEquivalenceReductionStatement : Prop :=
  RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v} →
    LeviSecondAdjointnessContragredientEquivalenceStatement.{u, v}

/-- All structural premises of the published second-adjointness and
Jacquet-contragredient reductions are discharged by existing proofs. The only
remaining premise here is uniform compression stabilization. -/
theorem leviSecondAdjointnessContragredientEquivalence_of_uniformCompression
    (hstab : RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v}) :
    LeviSecondAdjointnessContragredientEquivalenceStatement.{u, v} := by
  have hA := leviSecondAdjointness_of_structure.{u, v}
    parabolicDynamic oppositeDynamicParabolicUniqueness hstab
    Dynamic.leviAdjointDeterminantReciprocity
    RationalPointFamily.rationalReductiveUnimodularity standardCocharacter
    arbitraryParabolicQuotientCompact
  have hD := leviJacquetContragredient_of_structure.{u, max u v}
    parabolicDynamic oppositeDynamicParabolicUniqueness hstab
    Dynamic.leviAdjointDeterminantReciprocity
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP
  exact ⟨fun _ => hD k G hG P Pbar M N Nbar p m n hp hm hn hmul
      pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP,
    fun _ => hA k G hG P Pbar M N Nbar p m n hp hm hn hmul
      pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP⟩

/-- The internal reduction, packaged as its named proposition. -/
theorem leviSecondAdjointnessContragredientEquivalenceReduction :
    LeviSecondAdjointnessContragredientEquivalenceReductionStatement.{u, v} :=
  leviSecondAdjointnessContragredientEquivalence_of_uniformCompression

end Langlands.Aubert.General.RepresentedParabolic
