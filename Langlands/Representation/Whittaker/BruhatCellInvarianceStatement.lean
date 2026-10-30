import Langlands.Representation.Whittaker.BruhatCellDistribution
import Langlands.Representation.Whittaker.BruhatFiberAverage
import Langlands.HarmonicAnalysis.Distribution.CharacterAverage
import Langlands.HarmonicAnalysis.Distribution.Subspace
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Transpose invariance of bi-equivariant distributions on compatible Bruhat cells

A statement only. Over a p-adic field, let `C` be the upper Bruhat cell of a permutation
`w` in `GL_{n+1}`, `τ` the actual Weyl-conjugated transpose `g ↦ J * gᵀ * J`, and suppose
the character-compatible torus `compatibleTorus ψ n w` is nonempty. Then `τ` maps `C`
into itself, and every algebraic distribution on `C` that is bi-equivariant under the
upper unipotent group with the two positive standard-character factors is fixed by the
pushforward along the restriction of `τ` to `C`. This is an internal derived interface
for the case of a nonempty compatible locus in Shalika (1974), Proposition 1.8. See the
paired Markdown for the conventions, the intended proof and the provenance.
-/

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis MeasureTheory

universe uF

/-- For every prime `p`, every p-adic field `F : PadicField.{uF} p` with its canonical
normed field structure, every `n : ℕ`, every unitary additive character `ψ` of `F` and
every permutation `w` of `Fin (n + 1)` such that `compatibleTorus ψ n w` is nonempty,
there is a proof `hτ` that `weylTransposeHomeomorph n F` maps
`upperBruhatCell (n + 1) F w` into itself, and every algebraic distribution `D` on
`UpperBruhatCell (n + 1) F w` with `IsBiEquivariantBruhatCellDistribution n F w ψ D`
satisfies `IsWeylTransposeInvariantBruhatCellDistribution n F w hτ D`. -/
def BruhatCellInvarianceStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
      (w : Equiv.Perm (Fin (n + 1))),
      (compatibleTorus ψ n w).Nonempty →
        ∃ hτ : Set.MapsTo (weylTransposeHomeomorph n F.Carrier)
          (upperBruhatCell (n + 1) F.Carrier w)
          (upperBruhatCell (n + 1) F.Carrier w),
          ∀ D : Distribution (UpperBruhatCell (n + 1) F.Carrier w),
            IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D →
              IsWeylTransposeInvariantBruhatCellDistribution n F.Carrier w hτ D

end Langlands.Whittaker
