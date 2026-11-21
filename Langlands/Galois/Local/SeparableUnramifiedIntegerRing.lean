import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # The completed valuation ring of the maximal unramified extension -/

noncomputable section

namespace Langlands.LocalGalois.Separable.UnramifiedCompletion

open IsLocalRing ValuativeRel

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The adic completion of the actual integers of the inertia fixed field. -/
abbrev Integers := AdicCompletion (maximalIdeal (fixedFieldIntegers F)) (fixedFieldIntegers F)

end Langlands.LocalGalois.Separable.UnramifiedCompletion
