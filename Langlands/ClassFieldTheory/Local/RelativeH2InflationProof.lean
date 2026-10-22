import Langlands.ClassFieldTheory.Local.RelativeH2InflationStatement
import Langlands.ClassFieldTheory.Local.FiniteTowerCohomology
import Langlands.Cohomology.H2InflationProof

noncomputable section

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Inflation is injective and its range is the kernel of restriction
in every finite Galois tower. -/
theorem finiteRelativeH2InflationExactness :
    FiniteRelativeH2InflationExactness.{u} := by
  intro K L M _ _ _ _ _ _ _ _ _ _ _
  let C := groupCohomology.HInfRes (unitsRepresentation K M)
    (towerRestrictionKernel K L M) 2
  obtain ⟨hinj, hexact⟩ := Langlands.Cohomology.h2InflationRestrictionExactness
    IntegerScalars Gal(M/K) (unitsRepresentation K M)
    (towerRestrictionKernel K L M) (towerKernelH1_subsingleton K L M)
  let q := towerQuotientCohomologyIso K L M 2
  let e := towerKernelCohomologyIso K L M 2
  have hi : q.inv ≫ C.f = relativeInflation K L M 2 :=
    towerQuotientCohomologyIso_inflation K L M 2
  have hr : C.g ≫ e.hom = relativeRestriction K L M 2 :=
    towerKernelCohomologyIso_restriction K L M 2
  have hqi : Function.Injective q.inv :=
    (ModuleCat.mono_iff_injective q.inv).mp inferInstance
  have hqs : Function.Surjective q.inv :=
    (ModuleCat.epi_iff_surjective q.inv).mp inferInstance
  have hei : Function.Injective e.hom :=
    (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  constructor
  · rw [← hi]
    exact hinj.comp hqi
  · rw [← hi, ← hr]
    change LinearMap.range (C.f.hom.comp q.inv.hom) =
      LinearMap.ker (e.hom.hom.comp C.g.hom)
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hqs),
      LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hei)]
    exact hexact

end Langlands.ClassFieldTheory.Local
