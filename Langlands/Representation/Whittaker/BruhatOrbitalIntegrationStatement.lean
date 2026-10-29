import Langlands.Representation.Whittaker.BruhatFiberAverage

/-!
# Orbital integration from torus coordinates onto test functions on a Bruhat cell

The proposition `Langlands.Whittaker.BruhatOrbitalIntegrationStatement` asserts that, over
every canonical p-adic field, in every rank `n + 1` and for every permutation `w`, every
Haar measure `μ` on `U_w⁺ = permutationUnipotentPlus (n + 1) F w` that is also invariant
under right multiplication determines a unique complex-linear map `I` from test functions
on `M = U × (H × U)` to test functions on the actual upper Bruhat cell `C_w` such that
`I α (u₁ * p * h(d) * u₂) = ∫ u, α (u • (u₁, d, u₂)) ∂μ`, where the right side is the
published raw fiber average `bruhatFiberAverage`, and that this `I` is surjective and
sends `α` to a function whose topological support lies in the image of the topological
support of `α`. It is the nonarchimedean content of Shalika (1974), Lemma 1.10 together
with formula (1.11), printed p.176, in an internal formulation. This module defines an
unproved proposition. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis

universe uF

/-- For every prime `p`, every p-adic field `F : PadicField.{uF} p` with its canonical
normed-field structure, every `n : ℕ` and every permutation `w` of `Fin (n + 1)`, put
`U = upperUnipotent (n + 1) F`, `P = permutationUnipotentPlus (n + 1) F w`,
`H = Fin (n + 1) → Fˣ`, `M = U × (H × U)` and `C = UpperBruhatCell (n + 1) F w`, with
`P` carrying its Borel σ-algebra. For every Haar measure `μ` on `P` that is invariant
under right multiplication, there is exactly one complex-linear map
`I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C` such that
`I α (upperBruhatTorusMap (n + 1) w m) = bruhatFiberAverage (n + 1) F w μ α m` for all
`α` and `m`, `I` is surjective, and
`tsupport (I α) ⊆ upperBruhatTorusMap (n + 1) w '' tsupport α` for every `α`. -/
def BruhatOrbitalIntegrationStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (w : Equiv.Perm (Fin (n + 1))),
      let U := upperUnipotent (n + 1) F.Carrier
      let P := permutationUnipotentPlus (n + 1) F.Carrier w
      let H := Fin (n + 1) → F.Carrierˣ
      let M := U × (H × U)
      let C := UpperBruhatCell (n + 1) F.Carrier w
      letI := borel P
      ∀ (μ : Measure P) [Measure.IsHaarMeasure μ] [μ.IsMulRightInvariant],
        ∃! I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C,
          (∀ (α : SchwartzBruhat M) (m : M),
            I α (upperBruhatTorusMap (n + 1) w m) =
              bruhatFiberAverage (n + 1) F.Carrier w μ α m) ∧
          Function.Surjective I ∧
          (∀ α : SchwartzBruhat M,
            tsupport (I α : C → ℂ) ⊆
              upperBruhatTorusMap (n + 1) w '' tsupport (α : M → ℂ))

end Langlands.Whittaker
