import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing

/-!
# Invariant distributions near the central translates of the nilpotent cone

Harish-Chandra's Lemma 3.12, in the inductive proof of Theorem 3.1, for the Lie algebra `A` of
the unit group of a finite-dimensional semisimple algebra over a nonarchimedean local field `F`
of characteristic zero, with the center of `A` allowed
(`LieAlgebraCentralNilpotentDensityStatement`): assume Theorem 3.1 for every semisimple algebra
of smaller dimension. Let `f ∈ D₀` be annihilated, for every central `Z`, by every
conjugation-invariant distribution supported on `Z + N`, `N` the nilpotent cone. Then every
conjugation-invariant distribution annihilates `f`. The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §3.3–3.4, printed pp. 23–27: Theorem 3.1 is proved by induction on
`dim G`; Lemma 3.9 (Lemma 5) and Corollary 3.10 apply the induction hypothesis to the
centralizers of noncentral semisimple elements (Corollary 3.10: "Let `f` be an element in `D₀`
such that `Supp(f)` does not meet `z + N`. Then `T(f) = 0` for all `T ∈ J`"); after Lemma 3.11
reduces to semisimple `G`, Lemma 3.12 (Lemma 6) reads "Suppose `f ∈ D₀` such that `μ_O(f) = 0`
for all `O ∈ O(0)`. Then `T(f) = 0` for `T ∈ J`", proved by Lemmas 3.13–3.14. By Lemma 3.3 the
`μ_O` span `J(N)`; for a reductive group the orbits in `z + N` are the translates `Z + O`.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Lemma 3.12 under the induction hypothesis of Theorem 3.1**, with central
translates. For every nonarchimedean local field `F` of characteristic zero and every
finite-dimensional semisimple `F`-algebra `A` such that Theorem 3.1
(`RegularOrbitalDensityFor F B`) holds for every finite-dimensional semisimple `F`-algebra `B`
(in the universe of `A`) of smaller dimension: for every module topology on `A`, Borel
σ-algebra on `Aˣ` and Schwartz–Bruhat function `f` in `D₀` (`RegularOrbitalVanishing F A f`)
such that `S f = 0` for every central `Z` and every `S` in
`invariantSupportedIn {X | IsNilpotent (X - Z)}`, the conjugation-invariant distributions
supported on `Z + N`, every conjugation-invariant distribution `T` satisfies `T f = 0`. -/
def LieAlgebraCentralNilpotentDensityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A],
    (∀ (B : Type v) [Ring B] [Algebra F B] [FiniteDimensional F B] [IsSemisimpleRing B],
      Module.finrank F B < Module.finrank F A → RegularOrbitalDensityFor F B) →
    ∀ [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace Aˣ] [BorelSpace Aˣ],
      haveI := IsModuleTopology.isTopologicalRing F A
      ∀ f : SchwartzBruhat A, RegularOrbitalVanishing F A f →
        (∀ Z ∈ Subalgebra.center F A,
          ∀ S ∈ invariantSupportedIn {X : A | IsNilpotent (X - Z)}, S f = 0) →
        ∀ T : Distribution A, IsConjugationInvariant T → T f = 0

end Langlands.HarmonicAnalysis
