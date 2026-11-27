import Langlands.HarmonicAnalysis.UnitConjugation.HoweRestriction
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Howe's finiteness theorem on the Lie algebra of `Aˣ`

Howe's finiteness theorem (Harish-Chandra's Theorem 12.1, Theorem 2 of the original) for the
Lie algebra `A` of the unit group `Aˣ` of a finite-dimensional semisimple algebra over a
nonarchimedean local field `F` of characteristic zero: for a compact set `ω ⊆ A` and an open
additive subgroup `L` of `A`, the restrictions `j_L T` of the distributions `T ∈ J(ω)` to the
Schwartz–Bruhat functions invariant under translation by `L` (`restrictToLatticeTests L`) form a
finite-dimensional space (`LieAlgebraHoweFinitenessStatement`). The statement is not proved
here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed p. 2, Theorem 12.1 (Theorem 2 (Howe)):
"Let `ω` be a compact set in `g` and `L` a lattice in `g`. Then `dim j_L J(ω) < ∞`."
-/

namespace Langlands.HarmonicAnalysis

open UnitConjugation

/-- **Howe's finiteness theorem** (Harish-Chandra's Theorem 12.1) for the unit group of a
finite-dimensional semisimple algebra. For every nonarchimedean local field `F` of
characteristic zero, every finite-dimensional semisimple `F`-algebra `A` with its module
topology, every compact `ω ⊆ A` and every open additive subgroup `L` of `A`, the image of
`J(ω) = invariantSupportedIn ω` under the restriction `j_L = restrictToLatticeTests L` to the
`L`-invariant Schwartz–Bruhat functions is finite-dimensional: `dim j_L J(ω) < ∞`. -/
def LieAlgebraHoweFinitenessStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ω : Set A), IsCompact ω → ∀ (L : AddSubgroup A), IsOpen (L : Set A) →
      FiniteDimensional ℂ ((invariantSupportedIn ω).map (restrictToLatticeTests L))

end Langlands.HarmonicAnalysis
