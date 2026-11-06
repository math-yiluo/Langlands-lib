import Langlands.GroupScheme.IntegralModel.IntegralPointDescent
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.RingTheory.Valuation.Extension

/-! # Original integral points under an extension of valued fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology
open GaloisPointComparison

variable {F L : Type u} [Field F] [Field L]
  [ValuativeRel F] [ValuativeRel L] [Algebra F L] [ValuativeExtension F L]

private theorem canonicalValuationHasExtension :
    (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) where
  val_isEquiv_comap := by
    intro x y
    change ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y ↔
      ValuativeRel.valuation L (algebraMap F L x) ≤
        ValuativeRel.valuation L (algebraMap F L y)
    simp only [← Valuation.Compatible.vle_iff_le, ValuativeExtension.vle_iff_vle]

local instance : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) :=
  canonicalValuationHasExtension

/-- The extended integer ring meets the original field in its original integer ring. -/
theorem integerRange_intersection (x : F) :
    algebraMap F L x ∈ Set.range (algebraMap ↥𝒪[L] L) ↔
      x ∈ Set.range (algebraMap ↥𝒪[F] F) := by
  have integerRange {K : Type u} [Field K] [ValuativeRel K] (a : K) :
      a ∈ Set.range (algebraMap ↥𝒪[K] K) ↔
        ValuativeRel.valuation K a ≤ 1 := by
    constructor
    · rintro ⟨b, rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [integerRange, integerRange]
  exact Valuation.HasExtension.val_map_le_one_iff
    (ValuativeRel.valuation F) (ValuativeRel.valuation L) x

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G) (L)

/-- Base change of the supplied model along the actual inclusion of integer rings. -/
def baseChangeValued : IntegralModel ↥𝒪[L] L
    ((Langlands.GroupScheme.baseChange (Spec.algebraMap F L)).obj G) :=
  M.baseChange ↥𝒪[L] L

/-- The existing rational extension preserves and reflects the original integral image. -/
theorem mem_integralPoints_rationalExtend_iff_valued (g : rationalPoints G) :
    rationalExtend F L G g ∈ (M.baseChangeValued L).integralPoints ↔
      g ∈ M.integralPoints :=
  M.mem_integralPoints_rationalExtend_iff ↥𝒪[L] L
    (integerRange_intersection (L := L)) g

/-- Original integral points are the comap of the extended original-model image. -/
theorem integralPoints_eq_comap_baseChangeValued :
    M.integralPoints =
      (M.baseChangeValued L).integralPoints.comap (rationalExtend F L G) :=
  M.integralPoints_eq_comap_baseChange ↥𝒪[L] L
    (integerRange_intersection (L := L))

end Langlands.GroupScheme.IntegralModel
