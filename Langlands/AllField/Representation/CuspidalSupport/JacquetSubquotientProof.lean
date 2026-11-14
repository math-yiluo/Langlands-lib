import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetSubquotientStatement
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetExactnessProof
namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding NormalizedJacquetSubquotientTheorem normalizedJacquetSubquotient
open Langlands.AllField.CuspidalSupport

open _root_.Representation
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW

/-- Descending an injective/surjective presentation gives an actual Jacquet subquotient. -/
theorem normalizedJacquetSubquotient : NormalizedJacquetSubquotientTheorem.{uF, uV} := by
  intro F _ T n B
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A D hD
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hD
  refine SmoothRep.isSubquotient_iff_exists.mpr
    ⟨(T.normalizedJacquetFunctor B).obj C, (T.normalizedJacquetFunctor B).map i,
      (T.normalizedJacquetFunctor B).map q, ?_, ?_⟩
  · change Function.Injective (T.normalizedJacquetMap B (SmoothRep.hom i)).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_injective_of_smooth (Langlands.AllField.Parabolic.unipotentFiniteContainment F T B)
      _ hi (Langlands.AllField.Parabolic.isSmooth_radical F T B _ A.isSmooth)
  · change Function.Surjective (T.normalizedJacquetMap B (SmoothRep.hom q)).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_surjective _ hq

end Langlands.AllField.CuspidalSupport
