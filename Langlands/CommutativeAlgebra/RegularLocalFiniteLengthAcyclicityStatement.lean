import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Finite-length acyclicity over a regular local ring -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

namespace Langlands.CommutativeAlgebra

/-- A bounded finite free complex in nonnegative degrees over a regular
local ring, with maximal-ideal-power torsion homology, is acyclic below
the dimension of the ring. No upper term bound tied to the dimension is
required. -/
def RegularLocalFiniteLengthAcyclicityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (g : ℕ),
    ringKrullDim R = g →
    ∀ (C : CochainComplex (ModuleCat.{u} R) ℤ),
      IsFiniteFree C → C.IsStrictlyGE 0 →
      (∀ i : ℤ, ∃ N : ℕ, maximalIdeal R ^ N ≤ Module.annihilator R (C.homology i)) →
      ∀ i : ℤ, i < (g : ℤ) → IsZero (C.homology i)

end Langlands.CommutativeAlgebra
