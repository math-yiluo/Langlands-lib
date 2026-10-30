import Langlands.Representation.Whittaker.BruhatCellDistribution
import Langlands.Representation.Whittaker.BruhatFiberAverage
import Langlands.HarmonicAnalysis.Distribution.CharacterAverage
import Langlands.HarmonicAnalysis.Distribution.Subspace
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Vanishing of bi-equivariant distributions on character-incompatible Bruhat cells

A statement only. Over a p-adic field, let `C` be the upper Bruhat cell of a permutation
`w` in `GL_{n+1}` and suppose the character-compatible torus `compatibleTorus ψ n w` is
empty. Then every algebraic distribution on `C` that is bi-equivariant under the upper
unipotent group with the two positive standard-character factors is zero. This is an
internal derived interface for the case of an empty compatible locus in Shalika (1974),
Propositions 1.12–1.13 and the proof of Proposition 1.8. See the paired Markdown for the
conventions, the intended proof and the provenance.
-/

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis MeasureTheory

universe uF

/-- For every prime `p`, every p-adic field `F : PadicField.{uF} p` with its canonical
normed field structure, every `n : ℕ`, every bundled (continuous, nontrivial) unitary
additive character `ψ` of `F.Carrier` and every permutation `w` of `Fin (n + 1)` such that
`compatibleTorus ψ n w` is not nonempty, every algebraic distribution `D` on
`UpperBruhatCell (n + 1) F.Carrier w` with
`IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D` equals zero. -/
def BruhatCellVanishingStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
      (w : Equiv.Perm (Fin (n + 1))),
      ¬ (compatibleTorus ψ n w).Nonempty →
        ∀ D : Distribution (UpperBruhatCell (n + 1) F.Carrier w),
          IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D → D = 0

end Langlands.Whittaker
