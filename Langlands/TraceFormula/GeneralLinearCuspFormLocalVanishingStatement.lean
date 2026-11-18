import Langlands.BaseChange.CuspForm
import Langlands.Global.AdelicGL
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Langlands.Group.GL.BlockUnipotent

/-!
# Cusp forms at one finite place give vanishing two-block unipotent integrals

Let `K` be a number field, `v` a finite place of `K` and `f : GL_n(𝔸_K) → ℂ`. Write
`ι_v : GL_n(K_v) → GL_n(𝔸_K)` for the inclusion at `v` (identity at every other place).
Suppose that for all `x, y ∈ GL_n(𝔸_K)` the local slice `g ↦ f(x ι_v(g) y)` is a cusp form on
`GL_n(K_v)` in the sense of the Library's `Langlands.BaseChange.HasVanishingConstantTerms`.
Then for every split `a + b = n` with `a, b ≥ 1`, every Haar measure `dZ` on the `a × b`
matrices over `K_v` and all `x, y ∈ GL_n(𝔸_K)`,

`∫ f(x · ι_v([[1, Z], [0, 1]]) · y) dZ = 0`.

This is the local hypothesis of the cuspidal image statement for `GL_n` (Task 7577) and of the
radical vanishing statement for `GL_n` (Task 7581). It is a change of variables from the
unipotent radical of the two-block parabolic to its matrix coordinates. Derived content: it
connects the cusp-form condition at one place (Getz–Hahn 2024, Definition 16.4.1 and the proof
of Lemma 16.4.2, printed p. 430; Henniart–Lemaire 2011, II.6.3, printed p. 120, condition
`c_{v₁}(f)`) with the matrix-coordinate hypothesis of Tasks 7577 and 7581; see
`GeneralLinearCuspFormLocalVanishingStatement.md`.
-/

noncomputable section

open MeasureTheory
open Langlands.Global Langlands.GeneralLinear

namespace Langlands.TraceFormula

universe u

/-- If every two-sided adelic translate of `f`, restricted to the image of `GL_n(K_v)`, has
vanishing constant terms (`HasVanishingConstantTerms`), then the integral of `f` over every
two-sided translate of each upper two-block unipotent subgroup of `GL_n(K_v)` vanishes, for
every Haar measure on the matrix coordinates. -/
def GeneralLinearCuspFormLocalVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (v : Langlands.Global.FinitePlace K)
    (f : AdelicGL K n → ℂ),
    (∀ x y : AdelicGL K n, Langlands.BaseChange.HasVanishingConstantTerms
      (fun g : GeneralLinear n (FiniteCompletion K v) =>
        f (x * AdelicGL.ofFinite K n (FiniteAdelicGL.localInclusion K n v g) * y))) →
    ∀ (a b : ℕ) (h : a + b = n), 0 < a → 0 < b →
      letI : MeasurableSpace (Matrix (Fin a) (Fin b) (FiniteCompletion K v)) := borel _
      ∀ ν : Measure (Matrix (Fin a) (Fin b) (FiniteCompletion K v)), ν.IsAddHaarMeasure →
        ∀ x y : AdelicGL K n,
          ∫ Z, f (x * AdelicGL.ofFinite K n
            (FiniteAdelicGL.localInclusion K n v (blockUnipotent h Z)) * y) ∂ν = 0

end Langlands.TraceFormula
