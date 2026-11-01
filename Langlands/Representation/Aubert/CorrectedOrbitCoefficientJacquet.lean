import Langlands.Representation.Aubert.CorrectedOrbitCutIntegrals
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Parabolic.RefinementJacquetTransitivityProof
import Langlands.Representation.Parabolic.FlattenedJacquetComparisonProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalJacquetBlockBound

/-! Genuine orbit coefficient quotients as flattened Jacquet modules. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
  (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B)
  (hS : IsIntersectionRefinement (F := F.Carrier) B C w S)

/-- The representative-preserving linear equivalence from iterated normalized
Jacquet classes to the actual flattened Jacquet quotient. -/
def iteratedFlattenedJacquetEquiv :
    letI := T.topology
    RefinedJacquetModule B S (T.normalizedJacquet B A.representation) ≃ₗ[ℂ]
      (B.flatten S).JacquetModule A.representation := by
  let := T.topology
  exact (SmoothRep.equivOfIso
      (((Parabolic.normalizedRefinementJacquetTransitivity.{uF,uV} F T B S).choose).app A)
      ).toLinearEquiv.trans
    (((Parabolic.flattenedJacquetComparison.{uF,uF,uV}).2 F T B S A.representation).choose
      ).toLinearEquiv

theorem iteratedFlattenedJacquetEquiv_mk :
    letI := T.topology
    ∀ v : A,
      iteratedFlattenedJacquetEquiv T A B S
          (refinedJacquetMk B S (T.normalizedJacquet B A.representation)
            (B.jacquetMk A.representation v)) =
        (B.flatten S).jacquetMk A.representation v := by
  let := T.topology
  intro v
  change ((Parabolic.flattenedJacquetComparison.{uF,uF,uV}).2
      F T B S A.representation).choose
      (SmoothRep.hom
        (((Parabolic.normalizedRefinementJacquetTransitivity.{uF,uV} F T B S).choose).hom.app A)
        (refinedJacquetMk B S (T.normalizedJacquet B A.representation)
          (B.jacquetMk A.representation v))) = _
  rw [(Parabolic.normalizedRefinementJacquetTransitivity.{uF,uV} F T B S).choose_spec A v]
  exact ((Parabolic.flattenedJacquetComparison.{uF,uF,uV}).2
    F T B S A.representation).choose_spec v

/-- The genuine nested orbital coefficient of the actual induction-Jacquet
term is the flattened normalized Jacquet carrier. -/
def cutOrbitCoefficientJacquetEquiv :
    letI := T.topology
    Representation.Coinvariants (cutOrbitNestedCoefficient T A.representation C w B) ≃ₗ[ℂ]
      (B.flatten S).JacquetModule A.representation := by
  let := T.topology
  exact (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS
      (T.normalizedJacquet B A.representation)).trans
    (iteratedFlattenedJacquetEquiv T A B S)

/-- Both quotient stages send the class of an original vector to its class
for the flattened radical. -/
theorem cutOrbitCoefficientJacquetEquiv_mk_mk :
    letI := T.topology
    ∀ v : A,
      cutOrbitCoefficientJacquetEquiv T A B C w S hS
          (Representation.Coinvariants.mk (cutOrbitNestedCoefficient T A.representation C w B)
            (B.jacquetMk A.representation v)) =
        (B.flatten S).jacquetMk A.representation v := by
  let := T.topology
  intro v
  change iteratedFlattenedJacquetEquiv T A B S
    (T.parabolicOrbitNestedRefinedCoefficientEquiv B C w S hS
      (T.normalizedJacquet B A.representation)
      (Representation.Coinvariants.mk (cutOrbitNestedCoefficient T A.representation C w B)
        (B.jacquetMk A.representation v))) = _
  rw [T.parabolicOrbitNestedRefinedCoefficientEquiv_mk,
    iteratedFlattenedJacquetEquiv_mk]

include hS in
/-- Flattened Jacquet vanishing kills the actual nested orbit coefficient. -/
theorem cutOrbitCoefficient_subsingleton_of_flattened :
    letI := T.topology
    Subsingleton ((B.flatten S).JacquetModule A.representation) →
      Subsingleton (Representation.Coinvariants
        (cutOrbitNestedCoefficient T A.representation C w B)) := by
  let := T.topology
  intro h
  let := h
  exact (cutOrbitCoefficientJacquetEquiv T A B C w S hS).injective.subsingleton

end Langlands.Aubert.Support
