import Langlands.Correspondence.HenniartWeilElementaryLayer
import Langlands.Weil.Local.IntermediateWeil

/-!
# Fixed-cutoff tame averaging of Weil conductor counts

An intermediate formulation of the counting argument in Koch (1984), §8,
for the truncated tame reduction of the numerical LLC route.
-/

noncomputable section

namespace Langlands.Henniart

open LocalClassField Numerical

/-- The actual degree-`m` tame totally ramified intermediate fields of the
fixed algebraic closure of `K`. Conjugate but distinct fields are not identified. -/
def TameTotallyRamifiedExtensions.{uK} {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uK} p) (m : ℕ) :=
  {E : FiniteIntermediateExtension K.Carrier //
    IsTameTotallyRamifiedOfDegree K (E.asPadicField (p := p))
      (Weil.Local.intermediateEmbedding K E) m}

/-- Over the `m` actual degree-`m` tame totally ramified intermediate fields,
the sum of the pure-rank counts at cutoff `j` is `m` times the mixed-rank
count over `K` at that same cutoff. The equality takes place in `ℕ∞`. -/
def WeilTameAveragingStatement.{uK, uW} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (r m j : ℕ), ¬ p ∣ m →
    ∃ e : Fin m ≃ TameTotallyRamifiedExtensions K m,
      (∑ i : Fin m, weilConductorCount.{uK, uW} ((e i).1.asPadicField (p := p))
        (p ^ r - 1) j) = (m : ℕ∞) * weilConductorCount.{uK, uW} K (p ^ r * m - 1) j

/-- The fixed-cutoff average is sufficient for the published truncated reduction. -/
def WeilTameReductionFromAveragingStatement.{uK, uW} : Prop :=
  WeilTameAveragingStatement.{uK, uW} → WeilTameReductionStatement.{uK, uW}

end Langlands.Henniart
