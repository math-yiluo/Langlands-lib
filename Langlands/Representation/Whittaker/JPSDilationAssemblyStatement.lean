import Langlands.Representation.Whittaker.JPSFunctionSpace
import Langlands.HarmonicAnalysis.Basic

/-!
# JPS decomposition assembly from uniform coordinate dilations

An internal conditional assembly step for JPS (1979), Lemma (2.2.1). This module
defines a proposition only.
-/

namespace Langlands.Whittaker

open scoped BigOperators

open JPSFunctionSpace

universe uF

/-- Internal assembly helper for JPS (1979), Lemma (2.2.1): let `W` be a
translation-stable space of locally constant functions on `H = (Fˣ)ⁿ` with
coordinate upper support. Suppose that, in every coordinate `i`, one finite set
`Y i` of finite functions on `Fˣ` and one family `A i` of linear endomorphisms of
`W`, both chosen before every function, expand every bounded dilation
`b ↦ f (a * coordinateEmbedding i b)` with `|b| ≤ 1` on a region `|a_i| < ε`,
whose threshold depends on `f` but precedes the whole tuple `a` and all such `b`.
Then one finite set `X` of finite functions on `H`, chosen before the function,
expands every `f` in `W` with Schwartz–Bruhat coefficients on the whole additive
space `Fⁿ`. This is an internal derived target, not a printed JPS theorem. -/
def JPSDilationAssemblyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (W : FunctionSpace F n)
      (Y : Fin n → Finset (F.Carrierˣ → ℂ))
      (A : Fin n → (F.Carrierˣ → ℂ) → Module.End ℂ W.toSubmodule),
      IsLocallyConstantSpace W T →
      HasCoordinateUpperSupport W T →
      (∀ i : Fin n, ∀ η ∈ Y i, Continuous η ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))) →
      (∀ i : Fin n, ∀ f : W.toSubmodule,
        ∃ ε : ℝ, 0 < ε ∧
          ∀ a : Torus F n, T.normalizedAbs (a i : F.Carrier) < ε →
            ∀ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 →
              (coordinateRepresentation W i b f).val a =
                ∑ η ∈ Y i, η b * (A i η f).val a) →
      ∃ X : Finset (Torus F n → ℂ), (∀ χ ∈ X, IsFiniteFunction T χ) ∧
        ∀ f : W.toSubmodule,
          ∃ Φ : (Torus F n → ℂ) → HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier),
            ∀ a : Torus F n,
              f.val a = ∑ χ ∈ X, Φ χ (fun i => (a i : F.Carrier)) * χ a

end Langlands.Whittaker
