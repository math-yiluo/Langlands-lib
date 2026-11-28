import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing

/-!
# Invariant distributions supported on the nilpotent cone

Harish-Chandra's Lemma 3.3 for the Lie algebra `A` of the unit group of a finite-dimensional
semisimple algebra over a nonarchimedean local field `F` of characteristic zero: the space
`J(N)` of conjugation-invariant distributions supported on the nilpotent cone `N` is
finite-dimensional and spanned by the orbital distributions of nilpotent elements
(`LieAlgebraNilpotentInvariantSpanStatement`). The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §3.2, printed p. 19, Lemma 3.3 (Lemma 4): "The measures `μ_O`,
indexed by `O ∈ O(0)`, form a basis for `J(N)`", with the proof on printed pp. 19–22
(Lemmas 3.4–3.8); `O(0)`, the set of nilpotent orbits, is finite, and the orbital integrals
`μ_O` are defined by the theorem of Deligne and Ranga Rao (§3.1, printed p. 17).
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Lemma 3.3, spanning part.** For every nonarchimedean local field `F` of
characteristic zero and every finite-dimensional semisimple `F`-algebra `A` with its module
topology (and a Borel σ-algebra on `Aˣ`), the space `J(N) = invariantSupportedIn N` of
conjugation-invariant distributions on `A` supported on the nilpotent cone
`N = {X | IsNilpotent X}` is finite-dimensional, and it is contained in the complex span of
the orbital distributions `nilpotentOrbitals A` of nilpotent elements. -/
def LieAlgebraNilpotentInvariantSpanStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    FiniteDimensional ℂ (invariantSupportedIn {X : A | IsNilpotent X}) ∧
      invariantSupportedIn {X : A | IsNilpotent X} ≤ Submodule.span ℂ (nilpotentOrbitals A)

end Langlands.HarmonicAnalysis
