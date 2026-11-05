import Langlands.Geometry.Building.UnramifiedQuasiSplitReductionStatement
import Langlands.Geometry.Building.MaximalUnramifiedValuation

/-! # Applying generic Henselian quasi-splitness to the actual unramified field -/

universe u

namespace Langlands.Geometry.Building

namespace MaximalUnramified

open Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- Integer normalization preserves the published Henselian integer ring. -/
theorem valuationSubring_isHenselian :
    HenselianLocalRing (valuation F).valuationSubring := by
  rw [valuationSubring_eq F]
  exact fixedFieldIntegersIsHenselian F

/-- The actual residue of the integer-normalized valuation is algebraically
closed, using the published algebraic-closure theorem. -/
theorem residueField_isAlgClosed :
    IsAlgClosed (IsLocalRing.ResidueField (valuation F).valuationSubring) := by
  rw [valuationSubring_eq F]
  exact (fixedFieldResidueIsAlgClosure F).1

end MaximalUnramified

/-- Specialize the generic theorem without adding field hypotheses to the
published unramified assertion. -/
theorem unramifiedQuasiSplit_of_henselianDiscrete :
    UnramifiedQuasiSplitReductionStatement.{u} := by
  intro h F _ _ _ _ H hH
  exact h (UnramifiedClosure F) (MaximalUnramified.valuation F)
    (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F)
    (MaximalUnramified.residueField_isAlgClosed F) H hH

end Langlands.Geometry.Building
