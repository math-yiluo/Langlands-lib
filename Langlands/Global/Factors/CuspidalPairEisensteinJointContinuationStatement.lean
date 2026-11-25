import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.Factors.CuspidalPairEisensteinSeries

/-! # Joint continuation of the Eisenstein series induced from an actual cuspidal pair

The Eisenstein series `E(φ, s, g)` on `GL_(r+t+2)` induced from an actual cuspidal pair
continues meromorphically in `s`, with local denominators `(s - s₀)^m` that turn it into a
function of `(s, g)` that is jointly continuous, holomorphic in `s` and left `GL_(r+t+2)(F)`
invariant in `g`; on the line `Re s = 0` no denominator is needed. This is
Mœglin–Waldspurger IV.1.8, IV.1.9 (c)–(d) and IV.1.11 (a)–(b), restricted to the normalized
parameter line `s ↦ π ⊗ δ_P^(s/N)`. See the paired Markdown. -/

set_option autoImplicit false

universe u

namespace Langlands.Global

open NumberField CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters and a section `φ`
of the normalized induced representation from `π ⊗ π'^∨` on the upper two-block parabolic of
`GL_N`, `N = r + t + 2`, there are a function `E` of `(s, g)` and a real `σ` such that

* `E s` is the actual Eisenstein sum `eisensteinSeries F φ s` whenever `σ < Re s`;
* near every `s₀ ∈ ℂ` there are an exponent `m`, an open `W ∋ s₀` and a function `h` of
  `(s, g)`, continuous on `W × GL_N(𝔸)`, holomorphic in `s ∈ W` for every `g`, left invariant
  under `GL_N(F)` in `g`, with `h s g = (s - s₀)^m E s g` for `s ∈ W`, `s ≠ s₀`;
* if `Re s₀ = 0` one can take `m = 0`, and then also `h s₀ = E s₀`. -/
def CuspidalPairEisensteinJointContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ φ, IsSection T T' φ →
    ∃ (E : ℂ → AdelicGL F (r + t + 2) → ℂ) (σ : ℝ),
      (∀ s : ℂ, σ < s.re → E s = eisensteinSeries F (r := r) (t := t) φ s) ∧
      ∀ s₀ : ℂ, ∃ (m : ℕ) (W : Set ℂ) (h : ℂ → AdelicGL F (r + t + 2) → ℂ),
        IsOpen W ∧ s₀ ∈ W ∧
        ContinuousOn (fun q : ℂ × AdelicGL F (r + t + 2) => h q.1 q.2) (W ×ˢ Set.univ) ∧
        (∀ g, DifferentiableOn ℂ (fun s => h s g) W) ∧
        (∀ s ∈ W, ∀ (γ : RationalGL F (r + t + 2)) (g : AdelicGL F (r + t + 2)),
          h s (AdelicGL.rational F (r + t + 2) γ * g) = h s g) ∧
        (∀ s ∈ W, s ≠ s₀ → ∀ g, h s g = (s - s₀) ^ m * E s g) ∧
        (s₀.re = 0 → m = 0 ∧ ∀ g, h s₀ g = E s₀ g)

end Langlands.Global
