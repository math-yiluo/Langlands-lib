import Langlands.Algebra.BrauerCorestriction.CorResClass
import Langlands.ClassFieldTheory.Local.BrauerLocalInvariant
import Langlands.ClassFieldTheory.Local.InvariantRelativeCorestrictionProof
import Langlands.ClassFieldTheory.Local.SeparableClosureCorestrictionRestriction

noncomputable section

open Langlands.Brauer Langlands.BrauerComparison Langlands.BrauerCorestriction

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L : Type u) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
  [TopologicalSpace K] [TopologicalSpace L] [IsNonarchimedeanLocalField K]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/-- Every Brauer class over the upper local field comes from actual scalar extension. -/
theorem localBrauerScalarExtension_surjective (hcont : Continuous (algebraMap K L)) :
    Function.Surjective (scalarExtension (K := K) L) := by
  intro y
  obtain ⟨r, hr⟩ := rationalModIntegers_exists_nsmul_eq (Module.finrank K L)
    Module.finrank_pos (localBrauerInvariant L y)
  refine ⟨(localBrauerInvariant K).symm r, (localBrauerInvariant L).injective ?_⟩
  rw [localBrauerInvariant_scalarExtension K L hcont, AddEquiv.apply_symm_apply]
  exact hr

variable [Algebra.IsSeparable K L]

omit [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] in
/-- The actual continuous unit corestriction transported to Brauer classes. -/
def cohomologicalBrauerCorestriction : BrauerGroup.{u, u} L →+ BrauerGroup.{u, u} K :=
  (brauerEquiv K).symm.toAddMonoidHom.comp
    ((separableH2Corestriction K L).comp (brauerEquiv L).toAddMonoidHom)

/-- Serre's descent comparison identifies tensor-descent corestriction with continuous transfer. -/
theorem brauerEquiv_corestriction (hcont : Continuous (algebraMap K L))
    (y : BrauerGroup.{u, u} L) :
    brauerEquiv K (corHom K L y) = separableH2Corestriction K L (brauerEquiv L y) := by
  obtain ⟨x, rfl⟩ := localBrauerScalarExtension_surjective K L hcont y
  rw [corHom_scalarExtension, map_nsmul, brauerEquiv_scalarExtension,
    separableH2Corestriction_separableRestriction]

/-- The transported cohomological homomorphism equals the actual algebraic homomorphism. -/
theorem cohomologicalBrauerCorestriction_eq_corHom (hcont : Continuous (algebraMap K L)) :
    cohomologicalBrauerCorestriction K L = corHom K L := by
  ext y
  change (brauerEquiv K).symm (separableH2Corestriction K L (brauerEquiv L y)) = _
  rw [← brauerEquiv_corestriction K L hcont, AddEquiv.symm_apply_apply]

/-- Continuous corestriction preserves Serre's cohomological local invariant. -/
theorem separableLocalInvariant_corestriction (hcont : Continuous (algebraMap K L))
    (y : separableH2 L) :
    separableLocalInvariant K (separableH2Corestriction K L y) = separableLocalInvariant L y := by
  obtain ⟨z, rfl⟩ := (brauerEquiv L).surjective y
  obtain ⟨x, rfl⟩ := localBrauerScalarExtension_surjective K L hcont z
  rw [brauerEquiv_scalarExtension, separableH2Corestriction_separableRestriction,
    map_nsmul, separableLocalInvariant_restriction K L hcont]

/-- Actual tensor-descent corestriction preserves the value of the local invariant. -/
theorem localBrauerInvariant_corestriction (hcont : Continuous (algebraMap K L))
    (y : BrauerGroup.{u, u} L) :
    localBrauerInvariant K (corHom K L y) = localBrauerInvariant L y := by
  change separableLocalInvariant K (brauerEquiv K (corHom K L y)) =
    separableLocalInvariant L (brauerEquiv L y)
  rw [brauerEquiv_corestriction K L hcont, separableLocalInvariant_corestriction K L hcont]

end Langlands.ClassFieldTheory.Local
