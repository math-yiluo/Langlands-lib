import Langlands.Representation.Whittaker.BruhatFiberAverage
import Langlands.Representation.Whittaker.CompatibleTorus
import Langlands.HarmonicAnalysis.Distribution.CharacterAverage

/-!
# Character covariance of the product average under Shalika's fiber action

A statement only. For an actual p-adic field, a permutation `w` of `Fin (n + 1)` and the
standard character `χ` of the upper-unipotent group `U`, pulling a test function `α` on
`U × ((Fin (n + 1) → Fˣ) × U)` back along Shalika's action of `u ∈ U_w⁺` multiplies its
character average at `d` by the inverse of the published compatibility defect of `u` at `d`.
The measure on `U` is s-finite, finite on compact sets and both left and right invariant.
This is the computation of `β_{α^u}` in the proof of Shalika (1974), Proposition 1.13,
printed p.177. See the paired Markdown for the conventions, the sign and the provenance.
-/

namespace Langlands.Whittaker

open MeasureTheory
open Langlands.GeneralLinear HarmonicAnalysis

universe uF

/-- For every prime `p`, p-adic field `F` with its canonical normed-field structure, `n`,
unitary additive character `ψ` and permutation `w` of `Fin (n + 1)`, with
`U = upperUnipotent (n + 1) F`, `P = U_w⁺`, `H = Fin (n + 1) → Fˣ` and `M = U × (H × U)`,
and every s-finite Borel measure `μ` on `U` that is finite on compact sets and both left
and right invariant: for every test function `α` on `M`, `u ∈ P` and `d ∈ H`, the character
average of `m ↦ α (u • m)` at `d` is `(compatibilityDefect ψ n w u d)⁻¹` times the character
average of `α` at `d`. -/
def BruhatFiberCharacterCovarianceStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
      (w : Equiv.Perm (Fin (n + 1))),
      let U := upperUnipotent (n + 1) F.Carrier
      let P := permutationUnipotentPlus (n + 1) F.Carrier w
      let H := Fin (n + 1) → F.Carrierˣ
      let M := U × (H × U)
      letI := borel U
      letI : BorelSpace U := ⟨rfl⟩
      ∀ (μ : Measure U) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
        [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
        (α : SchwartzBruhat M) (u : P) (d : H),
        SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ
            (Hecke.TestFunction.pullback
              (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α) d =
          (compatibilityDefect ψ n w
              (Subgroup.inclusion
                (permutationUnipotentPlus_le_upperUnipotent (n + 1) F.Carrier w) u) d)⁻¹ *
            SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ α d

end Langlands.Whittaker
