import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Invariant open and closed neighbourhoods of compact sets in the Lie algebra of `Aˣ`

Harish-Chandra's Lemma 4.3 for the Lie algebra `A` of the unit group `Aˣ` of a
finite-dimensional semisimple algebra over a nonarchimedean local field `F` of characteristic
zero: every compact set `ω ⊆ A` lies in a set `D` that is open, closed and invariant under
conjugation by `Aˣ` (a `G`-domain) and is contained in the saturation `ω₀^G` of another compact
set `ω₀` (`LieAlgebraConjugationDomainStatement`). The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §2, printed p. 13: "By a `G`-domain in `g`, we mean a `G`-invariant
subset of `g` which is both open and closed"; §4, Lemma 4.3 (Lemma 10), printed p. 31: "Let `ω`
be a compact set in `g`. Then we can choose another compact set `ω₀` and a `G`-domain `D` in `g`
such that `ω₀^G ⊃ D ⊃ ω`."
-/

namespace Langlands.HarmonicAnalysis

open UnitConjugation

/-- **Harish-Chandra's Lemma 4.3** for the unit group of a finite-dimensional semisimple
algebra. For every nonarchimedean local field `F` of characteristic zero, every
finite-dimensional semisimple `F`-algebra `A` with its module topology and every compact
`ω ⊆ A`, there are a compact `ω₀ ⊆ A` and a set `D ⊆ A`, open and closed and invariant under
conjugation `X ↦ u X u⁻¹` by every unit `u`, with `ω ⊆ D ⊆ ⋃_u u ω₀ u⁻¹`. -/
def LieAlgebraConjugationDomainStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ω : Set A), IsCompact ω →
      ∃ ω₀ : Set A, IsCompact ω₀ ∧ ∃ D : Set A, IsClopen D ∧
        (∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) ∧
        ω ⊆ D ∧ D ⊆ conjugationSaturation ω₀

end Langlands.HarmonicAnalysis
