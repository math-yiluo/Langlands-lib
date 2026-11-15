import Langlands.Global.RankinSelberg.EqualIntegrals
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Analytic properties of the mirabolic Eisenstein series

For a nontrivial unitary character `ψ` of `F \ 𝔸`, an idele class character `η` and
`Φ ∈ S(𝔸^n)`: the Eisenstein series `E(g, Φ; s, η)` converges absolutely on a right
half-plane, continues to a function holomorphic off the finite set `P(η)` with at most simple
poles there, is bounded in vertical strips away from `P(η)` uniformly for `g` in compact
sets, and satisfies `E(g, Φ; s, η) = E(ᵗg⁻¹, Φ̂; 1 - s, η⁻¹)` (Cogdell 2004, p.209).
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance eisensteinSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance eisensteinSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- `f` is holomorphic off `P`, and at each `p ∈ P` it has at most a simple pole:
`(s - p) f(s)` is bounded on a punctured neighbourhood of `p`. -/
def HasAtMostSimplePolesIn (f : ℂ → ℂ) (P : Set ℂ) : Prop :=
  DifferentiableOn ℂ f Pᶜ ∧
    ∀ p ∈ P, ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ s : ℂ, s ≠ p → ‖s - p‖ < ε → ‖(s - p) * f s‖ ≤ C

/-- Cogdell 2004, §2.3, printed p.209: convergence, meromorphic continuation with at most
simple poles in `P(η)`, boundedness in vertical strips away from `P(η)` uniformly on compact
sets, and the functional equation of the mirabolic Eisenstein series. `η` is written `χ`. -/
def EisensteinStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) →
      let Φhat := fourierTransform F (r + 1) ψ Φ
      let transposeInv : Points F (r + 1) → Points F (r + 1) := fun g =>
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
          (GeneralLinear.inverseTranspose (r + 1) (Adeles F)
            (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g))
      ∃ σ₀ : ℝ, ∃ E Ehat : Points F (r + 1) → ℂ → ℂ,
        (∀ (g : Points F (r + 1)) (s : ℂ), σ₀ < s.re →
          Integrable (eisensteinSectionIntegrand F χ Φ s g) (ideleMeasure F) ∧
          Integrable (eisensteinSectionIntegrand F χ⁻¹ Φhat s g) (ideleMeasure F) ∧
          Summable (fun q : LeftCosetSpace (eisensteinParabolic F r) =>
            ‖eisensteinSection F χ Φ s (rationalPoint F (r + 1) q.out * g)‖) ∧
          Summable (fun q : LeftCosetSpace (eisensteinParabolic F r) =>
            ‖eisensteinSection F χ⁻¹ Φhat s (rationalPoint F (r + 1) q.out * g)‖) ∧
          E g s = eisensteinSeries F χ Φ s g ∧
          Ehat g s = eisensteinSeries F χ⁻¹ Φhat s g) ∧
        (∀ g : Points F (r + 1),
          HasAtMostSimplePolesIn (E g) (equalPoleSet F (r + 1) χ) ∧
          HasAtMostSimplePolesIn (Ehat g) (equalPoleSet F (r + 1) χ⁻¹)) ∧
        (∀ K : Set (Points F (r + 1)), IsCompact K →
          ∀ a b : ℝ, a ≤ b → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
            ∀ g ∈ K, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
              (∀ p ∈ equalPoleSet F (r + 1) χ, δ ≤ ‖s - p‖) → ‖E g s‖ ≤ C) ∧
        ∀ (g : Points F (r + 1)) (s : ℂ), s ∉ equalPoleSet F (r + 1) χ →
          E g s = Ehat (transposeInv g) (1 - s)

end Langlands.Global.RankinSelbergGlobal
