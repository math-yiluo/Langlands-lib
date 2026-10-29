import Langlands.Representation.Whittaker.BruhatFiberAverage
import Langlands.HarmonicAnalysis.Distribution.CharacterAverage
import Langlands.HarmonicAnalysis.Distribution.Subspace

/-!
# Support on the compatible torus from invariance under Shalika's fiber action

A statement only. Over a p-adic field, let `U` be the upper unipotent subgroup of
`GL_{n+1}`, `P = U_w⁺` for a permutation `w`, `H = Fin (n + 1) → Fˣ` and
`M = U × (H × U)`. If an algebraic distribution `τ` on `H` has a character-average dual
`τ ∘ characterAverage` that is invariant under pullback along every published fiber
homeomorphism `bruhatFiberActHomeomorph (n + 1) F w u`, `u ∈ P`, then `τ` is supported
on `compatibleTorus ψ n w`. This is an internal formulation of the support assertion in
Shalika (1974), Proposition 1.13. See the paired Markdown for the conventions, the
intended proof and the provenance.
-/

namespace Langlands.Whittaker

open MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis

universe uF

/-- For every prime `p`, every p-adic field `F : PadicField.{uF} p` with its canonical
normed field structure, every `n : ℕ`, every unitary additive character `ψ` of `F` and
every permutation `w` of `Fin (n + 1)`: let `U` be the upper unipotent subgroup of
`GL_{n+1}(F)` with its Borel σ-algebra, `P = permutationUnipotentPlus (n + 1) F w`,
`H = Fin (n + 1) → Fˣ` and `M = U × (H × U)`. For every Borel Haar measure `μ` on `U`
that is s-finite and right invariant and every algebraic distribution `τ` on `H`, if
`Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ` is invariant
under pullback along `bruhatFiberActHomeomorph (n + 1) F w u` for every `u : P`, then
`τ` lies in `Distribution.supportedOn (compatibleTorus ψ n w)`. -/
def BruhatCompatibleSupportStatement : Prop :=
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
      ∀ (μ : Measure U) [Measure.IsHaarMeasure μ] [SFinite μ]
        [μ.IsMulRightInvariant] (τ : Distribution H),
        (∀ (u : P) (α : SchwartzBruhat M),
          Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ
              (Hecke.TestFunction.pullback
                (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α) =
            Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ α) →
          τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)

end Langlands.Whittaker
