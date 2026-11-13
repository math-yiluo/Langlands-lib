import Langlands.Representation.Hecke.HomomorphismLeft
import Langlands.Algebra.NonUnitalModuleAdmissible

/-!
# Admissible representations and admissible Hecke modules (Renard III.1.7)

A smooth representation of a t.d. group is admissible if and only if its fixed vectors under
every compact open subgroup are finite-dimensional, and if and only if the corresponding
nondegenerate module over the Hecke algebra is admissible in the sense of I.5.1.
-/

namespace Langlands.Hecke

open MeasureTheory

universe u v

/-- Renard III.1.7, the paragraph after the Definition: for a t.d. group `G` with a left Haar
measure `μ` and a smooth complex representation `ρ`, (1) `ρ` is admissible if and only if
`V^K` is finite-dimensional for every compact open subgroup `K`, and (2) `ρ` is admissible if
and only if the nondegenerate `H(G)`-module `V` of III.1.4 is admissible in the sense of I.5.1
(every `e · V`, `e` an idempotent of `H(G)`, is finite-dimensional). -/
def AdmissibleIffHeckeAdmissibleStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ),
    (IsAdmissible ρ ↔ ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
        FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) ∧
      (IsAdmissible ρ ↔
        @Algebra.NonUnitalModuleAdmissible.IsAdmissible (HeckeAlgebra μ) _ _ _ _ V _
          (heckeNonUnitalModule μ ρ hρ) (Homomorphism.isIdempotented μ)
          (heckeNonUnitalModule_isNondegenerate μ ρ hρ))

end Langlands.Hecke
