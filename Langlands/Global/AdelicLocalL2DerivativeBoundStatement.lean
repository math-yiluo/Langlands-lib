import Langlands.Global.AdelicReproducingKernelStatement
import Langlands.Global.AdelicMaximalUnipotentDecay

/-! # Local `L²` bounds for the archimedean derivatives of `K_∞`- and `𝔷`-finite functions

`AdelicLocalL2DerivativeBoundStatement`: a left `G(F)`-invariant, smooth, `K_∞`-finite and
`𝔷`-finite function `Φ` on `G(𝔸)` (the functions of `AdelicReproducingKernelStatement`) satisfies,
for every word `D` of archimedean right-orbit derivatives, `|D Φ(g)|² ≤ C ∫_S |Φ(g s)|² ds` for
one compact set `S ⊆ G(𝔸)` and one constant `C`, uniformly in `g ∈ G(𝔸)`. It is the consequence
of Harish-Chandra's smooth reproducing kernel (Harish-Chandra 1966, §8, Theorem 1) obtained by
differentiating `Φ = Φ * α` under the integral and applying the Cauchy–Schwarz inequality. It
differs from the Sobolev estimate of Bernstein's Key Lemma (Bernstein 1988, §3.4), which bounds
`|f(x)|²` by the local integral of a sum of squares of derivatives of `f`: here every derivative is
bounded by the local `L²` mass of `Φ` itself. This file states the proposition and does not prove
it. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

/-- **Local `L²` bounds for the archimedean derivatives of `K_∞`- and `𝔷`-finite functions**
(derived from Harish-Chandra 1966, §8, Theorem 1, in the adelic form of Mœglin–Waldspurger
I.2.17, Lemma, by differentiation of the smooth kernel and the Cauchy–Schwarz inequality). Let
`G` be a connected reductive group over a number field `F`, `K` a maximal compact subgroup of
`G(𝔸)` and
`K_∞ = K.comap (ofInfinite F G)` its archimedean part. Let `Φ : G(𝔸) → ℂ` be left
`G(F)`-invariant, smooth (`IsAdelicSmoothFunction`), `K_∞`-finite and `𝔷`-finite. Then for every
word `D` of tangent directions of `G(F_∞)` there are a compact `S ⊆ G(𝔸)` and `C ≥ 0` with
`‖D Φ(g)‖² ≤ C ∫_S ‖Φ(g s)‖² ds` for every `g ∈ G(𝔸)`, where
`D Φ = adelicIteratedDirectionalValue hsmooth D Φ` is the iterated right-orbit derivative and the
integral is the lower Lebesgue integral for the Haar measure `Measure.haar` of `G(𝔸)`. -/
def AdelicLocalL2DerivativeBoundStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {d : ℕ}
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K →
    ∀ Φ : AdelicGroupPoints F G → ℂ,
      IsLeftInvariantUnder F G (rationalSubgroup F G) Φ →
      IsAdelicSmoothFunction F G Φ →
      IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) Φ →
      IsCenterFiniteFunction F G hsmooth hcalc Φ →
      ∀ D : List (smoothModel F d), ∃ (S : Set (AdelicGroupPoints F G)) (C : ℝ≥0),
        IsCompact S ∧ ∀ g : AdelicGroupPoints F G,
          ‖adelicIteratedDirectionalValue hsmooth D Φ g‖ₑ ^ 2 ≤
            (C : ℝ≥0∞) * ∫⁻ s in S, ‖Φ (g * s)‖ₑ ^ 2
              ∂(Measure.haar : Measure (AdelicGroupPoints F G))

end Langlands.Global
