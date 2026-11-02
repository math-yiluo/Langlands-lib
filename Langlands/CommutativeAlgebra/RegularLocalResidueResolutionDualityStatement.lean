import Langlands.CommutativeAlgebra.FiniteFreeReversedDual
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Top dual homology of a residue-field resolution -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

namespace Langlands.CommutativeAlgebra

/-- A finite free resolution of the residue field, written in degrees
`0, …, g` with its homology in degree `g`, has residue field as the top
homology of its reversed dual over a regular local ring of dimension `g`. -/
def RegularLocalResidueResolutionDualityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (g : ℕ),
    ringKrullDim R = g →
    ∀ (C : CochainComplex (ModuleCat.{u} R) ℤ),
      IsFiniteFree C → C.IsStrictlyGE 0 → C.IsStrictlyLE (g : ℤ) →
      (∀ i : ℤ, i ≠ (g : ℤ) → IsZero (C.homology i)) →
      Nonempty (C.homology (g : ℤ) ≅ ModuleCat.of R (ResidueField R)) →
      Nonempty ((reversedDual (g : ℤ) C).homology (g : ℤ) ≅
        ModuleCat.of R (ResidueField R))

end Langlands.CommutativeAlgebra
