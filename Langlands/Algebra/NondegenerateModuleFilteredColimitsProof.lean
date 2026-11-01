import Langlands.Algebra.NondegenerateModuleFilteredColimitsStatements
import Langlands.Algebra.NondegenerateModuleExactnessProof
import Langlands.Algebra.NonUnitalModuleDirectSum
import Langlands.CategoryTheory.RenardCompletenessLimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! Exact filtered colimits through the actual original inclusion. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NondegenerateModuleFilteredColimitsProof

open NondegenerateModuleFilteredColimitsStatements

universe uA uI uM

variable {A : Type uA} [NonUnitalRing A]

/-- Actual finite-support sums and abelian coequalizers supply filtered colimits. -/
theorem filteredColimits (hA : IsIdempotented A) :
    HasFilteredColimitsOfSize.{uI, uI}
      (NondegenerateModuleCat.{uA, max uI uM} A) := by
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  let hc : HasCoproducts.{uI} (NondegenerateModuleCat.{uA, max uI uM} A) :=
    hasCoproducts_of_colimit_cofans
      (fun P => NonUnitalModuleDirectSum.cofan.{uA, uI, uM} hA P)
      (fun P => NonUnitalModuleDirectSum.cofanIsColimit.{uA, uI, uM} hA P)
  let : HasColimitsOfSize.{uI, uI}
      (NondegenerateModuleCat.{uA, max uI uM} A) :=
    Langlands.Renard.sourceCocompleteHasColimits.{uI}
      (NondegenerateModuleCat.{uA, max uI uM} A) hc
  infer_instance

/-- Exactness pulled back through integer unitization and original inclusion. -/
noncomputable abbrev exactFilteredColimits (hA : IsIdempotented A) :
    letI := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
    letI := filteredColimits.{uA, uI, uM} hA
    AB5OfSize.{uI, uI} (NondegenerateModuleCat.{uA, max uI uM} A) := by
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  let := filteredColimits.{uA, uI, uM} hA
  constructor
  intro J _ _
  let : AB5OfSize.{uI, uI} (AddCommGrpCat.{max uI uM}) :=
    AB5OfSize_shrink _
  let : HasExactColimitsOfShape J (ModuleCat.{max uI uM} (Unitization ℤ A)) :=
    HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{max uI uM} (Unitization ℤ A)) AddCommGrpCat)
  let : HasColimitsOfShape J (NonUnitalModuleCat.{uA, max uI uM} A) :=
    Adjunction.hasColimitsOfShape_of_equivalence
      (IntegerUnitization.equivalence.{uA, max uI uM} A).functor
  let : HasExactColimitsOfShape J (NonUnitalModuleCat.{uA, max uI uM} A) :=
    HasExactColimitsOfShape.domain_of_functor J
      (IntegerUnitization.equivalence.{uA, max uI uM} A).functor
  let := nondegenerateInclusion_preservesHomology.{uA, max uI uM} hA
  let : PreservesFiniteLimits (nondegenerateInclusion.{uA, max uI uM} A) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesColimitsOfSize.{uI, uI}
      (nondegenerateInclusion.{uA, max uI uM} A) :=
    (nondegeneratePartAdjunction hA).leftAdjoint_preservesColimits
  exact HasExactColimitsOfShape.domain_of_functor J (nondegenerateInclusion A)

/-- The actual category has Mathlib's AB5 certificate and filtered colimits. -/
theorem mathlibAB5 : MathlibAB5Statement.{uA, uI, uM} := by
  intro A _ hA
  exact ⟨filteredColimits hA, ⟨exactFilteredColimits hA⟩⟩

/-- Pointwise short exact systems yield a short exact sequence of actual colimits. -/
theorem shortExactColimits : ShortExactColimitsStatement.{uA, uI, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uI uM} A hA
  refine ⟨filteredColimits.{uA, uI, uM} hA, ?_⟩
  let := filteredColimits.{uA, uI, uM} hA
  let := exactFilteredColimits.{uA, uI, uM} hA
  intro J _ _ S hS
  have hf (j : J) : Mono (S.f.app j) := (hS j).mono_f
  have hg (j : J) : Epi (S.g.app j) := (hS j).epi_g
  have hE : S.Exact := by
    have he (j : J) := (hS j).exact
    simp only [ShortComplex.exact_iff_isZero_homology] at he ⊢
    rw [IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext j
    apply (IsZero.of_iso (he j)
      (S.mapHomologyIso ((evaluation J (NondegenerateModuleCat A)).obj j)).symm).eq_of_src
  let : Mono S.f := NatTrans.mono_of_mono_app S.f
  let : Epi S.g := NatTrans.epi_of_epi_app S.g
  have hSE : S.ShortExact := { exact := hE }
  exact hSE.map_of_exact colim

/-- Both exact closed filtered-colimit assertions. -/
theorem filteredColimitAssertions : FilteredColimitAssertions.{uA, uI, uM} :=
  ⟨mathlibAB5, shortExactColimits⟩

example : FilteredColimitAssertions.{uA, uI, uM} :=
  filteredColimitAssertions.{uA, uI, uM}

example : FilteredColimitAssertions.{0, 1, 2} := filteredColimitAssertions.{0, 1, 2}
example : FilteredColimitAssertions.{0, 2, 1} := filteredColimitAssertions.{0, 2, 1}
example : FilteredColimitAssertions.{1, 0, 2} := filteredColimitAssertions.{1, 0, 2}
example : FilteredColimitAssertions.{1, 2, 0} := filteredColimitAssertions.{1, 2, 0}
example : FilteredColimitAssertions.{2, 0, 1} := filteredColimitAssertions.{2, 0, 1}
example : FilteredColimitAssertions.{2, 1, 0} := filteredColimitAssertions.{2, 1, 0}

end Langlands.Algebra.NondegenerateModuleFilteredColimitsProof
