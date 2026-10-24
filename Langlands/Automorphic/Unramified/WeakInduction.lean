import Langlands.Representation.Unramified.SpectralSystem
import Langlands.Global.HeckeCharacter
import Langlands.Global.AdelicFunctoriality.Norm

/-!
# Weak induction of a Hecke character on unramified spectra

The unramified condition in Harris's weak automorphic induction (Definition 1.3(b)),
stated for a numerical spectral system of the base field and a Hecke character of a
finite extension. Following Tate's restriction formula for induced representations,
the comparison runs over all places above each base place. No cuspidal object,
ramified compatibility or existence is involved.
-/

noncomputable section

universe uE uE'

namespace Langlands.Automorphic.Unramified.WeakInduction

open Polynomial Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField

variable {E : Type uE} {E' : Type uE'} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E']

/-- A family of uniformizers of the completions at the places above `v`. -/
def IsUniformizerFamily (v : FinitePlace E)
    (ϖ : ∀ w : FinitePlacesAbove E' v, (FiniteCompletion E' w.1)ˣ) : Prop :=
  ∀ w, Valued.v ((ϖ w : (FiniteCompletion E' w.1)ˣ) : FiniteCompletion E' w.1) =
    WithZero.exp (-1 : ℤ)

/-- Every place above `v` is unramified in `E'/E`, and the Hecke character is
unramified there. -/
def IsUnramifiedAbove (χ : HeckeCharacter E') (v : FinitePlace E) : Prop :=
  ∀ w : FinitePlacesAbove E' v,
    w.1.asIdeal.ramificationIdx (𝓞 E) = 1 ∧ χ.IsUnramifiedAt w.1

/-- The Euler denominator at `v` of the induction of `χ`, in `X = q_v ^ (-s)`:
the product over the places `w` above `v` of `1 - χ_w(ϖ_w) X ^ f(w|v)`. -/
def inducedEulerPolynomial (χ : HeckeCharacter E') (v : FinitePlace E)
    (ϖ : ∀ w : FinitePlacesAbove E' v, (FiniteCompletion E' w.1)ˣ) : Polynomial ℂ :=
  ∏ w : FinitePlacesAbove E' v,
    (1 - C ((χ.finiteComponent w.1 (ϖ w) : ℂˣ) : ℂ) *
      X ^ (w.1.asIdeal.inertiaDeg (𝓞 E)))

end Langlands.Automorphic.Unramified.WeakInduction

namespace Langlands.Unramified.SpectralSystem

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.Unramified.WeakInduction

variable {E : Type uE} {E' : Type uE'} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E']

/-- The spectral system has rank `[E' : E]` and, at all but finitely many finite
places `v` of `E`, both `E'/E` and `χ` are unramified above `v` and the Euler
denominator at `v` equals that of the induction of `χ`, for every family of
uniformizers above `v`. -/
def IsWeakInductionOf {n : ℕ} (s : SpectralSystem (FinitePlace E) n)
    (χ : HeckeCharacter E') : Prop :=
  n = Module.finrank E E' ∧
    ∀ᶠ v in Filter.cofinite, ∀ hv : v ∉ s.exceptional, IsUnramifiedAbove χ v ∧
      ∀ ϖ : ∀ w : FinitePlacesAbove E' v, (FiniteCompletion E' w.1)ˣ,
        IsUniformizerFamily v ϖ → s.eulerPolynomial v hv = inducedEulerPolynomial χ v ϖ

end Langlands.Unramified.SpectralSystem
