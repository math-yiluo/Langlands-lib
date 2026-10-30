import Langlands.Representation.Whittaker.BruhatCellDistribution
import Langlands.Representation.Whittaker.BruhatFiberAverage
import Langlands.HarmonicAnalysis.Distribution.CharacterAverage
import Langlands.HarmonicAnalysis.Distribution.Subspace
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Factorization of a bi-equivariant cell distribution over the compatible torus

A statement only. Over a p-adic field, let `U` be the upper unipotent subgroup of
`GL_{n+1}`, `P = U_w⁺` for a permutation `w`, `H = Fin (n + 1) → Fˣ`, `M = U × (H × U)`
and `C` the upper Bruhat cell of `w`, as a subtype of the matrix group. Let `I` be a
complex-linear map from test functions on `M` to test functions on `C` whose value at
`u₁ * p_w * h(d) * u₂` is the published raw fiber average `∫ α (u • (u₁, (d, u₂))) dν(u)`.
If an algebraic distribution `D` on `C` is bi-equivariant under the upper unipotent group
with the two positive standard-character factors, then there is a unique algebraic
distribution `τ` on `H`, supported on `compatibleTorus ψ n w`, with
`τ ∘ characterAverage χ μ = D ∘ I`. This is an internal derived interface combining
Shalika (1974), Lemma 1.10, formula (1.11) and Propositions 1.12 and 1.13. See the paired
Markdown for the conventions, the intended proof and the provenance.
-/

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis MeasureTheory

universe uF

/-- For every prime `p`, every p-adic field `F : PadicField.{uF} p` with its canonical
normed field structure, every `n : ℕ`, every unitary additive character `ψ` of `F` and
every permutation `w` of `Fin (n + 1)`: let `U` be the upper unipotent subgroup of
`GL_{n+1}(F)`, `P = permutationUnipotentPlus (n + 1) F w`, `H = Fin (n + 1) → Fˣ`,
`M = U × (H × U)` and `C = UpperBruhatCell (n + 1) F w`, with Borel σ-algebras on `U`
and `P`. For every s-finite right-invariant Haar measure `μ` on `U`, every right-invariant
Haar measure `ν` on `P` and every complex-linear map `I` from test functions on `M` to
test functions on `C` with `I α (upperBruhatTorusMap (n + 1) w m) =
bruhatFiberAverage (n + 1) F w ν α m` for all `α` and `m`, every algebraic distribution
`D` on `C` with `IsBiEquivariantBruhatCellDistribution n F w ψ D` has a unique algebraic
distribution `τ` on `H` with `τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)` and
`Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ = D.comp I`. -/
def BruhatCellFactorizationStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (ψ : UnitaryAdditiveCharacter F.Carrier)
      (w : Equiv.Perm (Fin (n + 1))),
      let U := upperUnipotent (n + 1) F.Carrier
      let P := permutationUnipotentPlus (n + 1) F.Carrier w
      let H := Fin (n + 1) → F.Carrierˣ
      let M := U × (H × U)
      let C := UpperBruhatCell (n + 1) F.Carrier w
      letI := borel U
      letI : BorelSpace U := ⟨rfl⟩
      letI := borel P
      ∀ (μ : Measure U) [Measure.IsHaarMeasure μ] [SFinite μ]
        [μ.IsMulRightInvariant]
        (ν : Measure P) [Measure.IsHaarMeasure ν] [ν.IsMulRightInvariant]
        (I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C),
        (∀ (α : SchwartzBruhat M) (m : M),
          I α (upperBruhatTorusMap (n + 1) w m) =
            bruhatFiberAverage (n + 1) F.Carrier w ν α m) →
        ∀ D : Distribution C,
          IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D →
          ∃! τ : Distribution H,
            τ ∈ Distribution.supportedOn (compatibleTorus ψ n w) ∧
              Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ =
                D.comp I

end Langlands.Whittaker
