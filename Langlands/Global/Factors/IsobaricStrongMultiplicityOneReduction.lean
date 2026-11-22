import Langlands.Automorphic.CuspidalComplexPlaceParameterUniqueness
import Langlands.Automorphic.CuspidalRealPlaceParameterUniqueness
import Langlands.Automorphic.IsobaricArchimedeanParameterComparison
import Langlands.Automorphic.LocalComponentDeterminationFromAdmissibleTypes
import Langlands.Global.Factors.IsobaricInducingDataRecovery
import Langlands.Global.Factors.IsobaricPlaceComponents
import Langlands.Global.Factors.IsobaricStrongMultiplicityOneStatement
import Langlands.Representation.Archimedean.RealDiscreteCoincidentProof
import Langlands.Representation.Archimedean.RealDiscreteSeparatedProof
import Langlands.Representation.Archimedean.RealLeviChartIntegrable
import Langlands.Representation.Archimedean.RealLeviLanglandsQuotient
import Langlands.Representation.Archimedean.RealLeviParabolicIntegration
import Langlands.Representation.Archimedean.RealTemperedFormProof
import Langlands.Representation.Archimedean.RealTiedScalarAssembly

/-! # Isobaric strong multiplicity one from inducing-data and real parameter uniqueness -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open Langlands.Automorphic Langlands.Archimedean

/-- Strong multiplicity one follows from inducing-data rigidity and
real standard-module parameter uniqueness. -/
def IsobaricStrongMultiplicityOneReductionStatement : Prop :=
  CuspidalInducingDataRigidityStatement.{u, uQ} →
    RealStandardIsotypicParameterUniquenessStatement.{u, u} →
    IsobaricStrongMultiplicityOneStatement.{u, uQ}

theorem isobaricStrongMultiplicityOne_of_rigidity_and_real_parameters :
    IsobaricStrongMultiplicityOneReductionStatement.{u, uQ} := by
  intro rigidity realParameters
  have hScalar : RealTemperedScalarCommutantStatement :=
    realTemperedScalarCommutant_of_cases
      (realTiedNondiscreteReduction RealSphericalCyclicProof.realSphericalCyclic)
      (realTiedDiscreteScalarCommutant_of_cases realTiedDiscreteSeparatedScalarCommutant
        realTiedDiscreteCoincidentScalarCommutant)
  have hTempered : RealTemperedStandardIrreducibleStatement :=
    realTemperedStandardIrreducible_of_form_of_scalarCommutant realTemperedForm hScalar
  have realQuotients : RealStandardLanglandsQuotientStatement :=
    realLeviLanglandsQuotient realLeviChartIntegrable realLeviParabolicIntegration hTempered
  intro F _ _ _ r Q Q' hQ hQ' S hCommon
  obtain ⟨k, m, hm, T, P, h, hSum⟩ := hQ
  obtain ⟨k', m', hm', T', P', h', hSum'⟩ := hQ'
  obtain ⟨e, hc⟩ := exists_cuspidalMatching_of_common_finitePlace_embeddings
    rigidity hm hm' hSum hSum' S hCommon
  let c (i : Fin k) : PositiveRankCuspidalClass F := ⟨m i, (T i).isoClass⟩
  let c' (j : Fin k') : PositiveRankCuspidalClass F := ⟨m' j, (T' j).isoClass⟩
  refine nonempty_equivalence_of_common_admissible_localComponents Q Q'
    (IrreducibleOperatorSubquotient.exists_common_finitePlace_isotypic_of_isobaricSum
      hSum hSum' e hc) ?_ ?_
  · intro v
    obtain ⟨d, hd, ds, hds, hL⟩ := hSum.2.1 v
    obtain ⟨d', hd', es, hes, hL'⟩ := hSum'.2.1 v
    have hp : (realMoeglinData ds).Perm (realMoeglinData es) :=
      perm_expanded_pooled_parameters_of_matched_classes
        (fun C xs => C.HasRealPlaceParameter v xs) realBlockMoeglinData
        (fun C _ _ hA hB => C.realPlaceParameters_perm realParameters v hA hB)
        c c' e hc hd hd' hds hes
    obtain ⟨V, ρ, π, hGK, hadm, hirr, hI, hI'⟩ :=
      IrreducibleOperatorSubquotient.common_realPlaceIsotypic_of_moeglin_perm
        realQuotients v hL hL' hp
    exact ⟨V, ρ, π, hGK, hirr, hadm, hI, hI'⟩
  · intro v
    obtain ⟨d, hd, ds, hds, hL⟩ := hSum.2.2 v
    obtain ⟨d', hd', es, hes, hL'⟩ := hSum'.2.2 v
    have hflat (xs : List Langlands.LocalFactor.Archimedean.ComplexCharacterData) :
        xs.flatMap (fun x => [x]) = xs := by
      change xs.flatMap (fun x => [id x]) = xs
      rw [← List.map_eq_flatMap, List.map_id]
    have hp : ds.Perm es := by
      simpa only [hflat] using
        (perm_expanded_pooled_parameters_of_matched_classes
          (fun C xs => C.HasComplexPlaceParameter v xs) (fun x => [x])
          (fun C _ _ hA hB => by
            simpa only [hflat] using C.complexPlaceParameters_perm v hA hB)
          c c' e hc hd hd' hds hes)
    obtain ⟨V, ρ, π, hGK, hadm, hirr, hI, hI'⟩ :=
      IrreducibleOperatorSubquotient.common_complexPlaceIsotypic_of_perm v hL hL' hp
    exact ⟨V, ρ, π, hGK, hirr, hadm, hI, hI'⟩

end Langlands.Global
