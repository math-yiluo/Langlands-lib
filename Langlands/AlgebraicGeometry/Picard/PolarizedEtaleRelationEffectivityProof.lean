import Langlands.AlgebraicGeometry.Picard.PolarizedEtaleRelationEffectivityStatement
import Langlands.AlgebraicGeometry.Picard.EtaleRelationQuasiAffineEffectivity
import Langlands.AlgebraicGeometry.Picard.EquivariantSectionDescent
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof

/-! # Effective polarized scheme descent for a cartesian étale relation: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- Effective polarized scheme descent for a cartesian étale relation over an affine étale
cover. -/
theorem polarizedEtaleRelationEffectivity : PolarizedEtaleRelationEffectivityStatement.{u} := by
  intro S U hS hU p hpet hpsurj E f _ _ hcart B hB
  have : CompactSpace E.U := hB.compactSpace
  have : QuasiSeparatedSpace E.U := hB.quasiSeparatedSpace
  refine EtaleRelationQuasiAffineEffectivity.exists_effective_of_invariantQuasiAffine hcart ?_
  intro x
  obtain ⟨n, hn, σ, hxσ, -⟩ := hB.exists_section x
  obtain ⟨c, hxc, hinv⟩ := EquivariantModule.exists_invariant_section p f hcart
    (tensorPow B.bundle.obj n) (tensorPow_isLocallyFreeRankOne E.U B.bundle n)
    (B.tensorPowModule n) σ x hxσ
  exact ⟨B.bundle.sectionOpen c, hxc, hinv, hB.quasiAffine_sectionOpen hn c⟩

end Langlands.AlgebraicGeometry.Picard
