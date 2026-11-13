import Langlands.Representation.Whittaker.JPSDilationAssemblyStatement
import Langlands.AllField.Representation.Whittaker.JPSFunctionSpace
/-!
# JPS decomposition assembly from uniform coordinate dilations

An internal conditional assembly step for JPS (1979), Lemma (2.2.1). This module
defines a proposition only.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding JPSDilationAssemblyStatement
open Langlands.AllField.Whittaker

open scoped BigOperators

open Langlands.Whittaker.JPSFunctionSpace hiding CoordinateGerm FunctionSpace HasCoordinateUpperSupport HasFiniteCoordinateOperatorSpan HasFiniteOperatorSpans IsFiniteFunction IsLocallyConstantSpace Torus VanishesNearCoordinateZero coordinateEmbedding coordinateEmbedding_apply coordinateEmbedding_same coordinateRepresentation coordinateRepresentation_apply coordinateVanishing germMap germMap_eq_zero_iff germMap_surjective germRepresentation germRepresentation_apply_mk mul_coordinateEmbedding sigma sigma_apply_mk translate_apply vanishesNearCoordinateZero_add vanishesNearCoordinateZero_smul vanishesNearCoordinateZero_translate vanishesNearCoordinateZero_zero
open Langlands.AllField.Whittaker.JPSFunctionSpace

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
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (W : FunctionSpace F n)
      (Y : Fin n → Finset (Fˣ → ℂ))
      (A : Fin n → (Fˣ → ℂ) → Module.End ℂ W.toSubmodule),
      IsLocallyConstantSpace W T →
      HasCoordinateUpperSupport W T →
      (∀ i : Fin n, ∀ η ∈ Y i, Continuous η ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fˣ => fun a : Fˣ => η (b * a)))) →
      (∀ i : Fin n, ∀ f : W.toSubmodule,
        ∃ ε : ℝ, 0 < ε ∧
          ∀ a : Torus F n, T.normalizedAbs (a i : F) < ε →
            ∀ b : Fˣ, T.normalizedAbs (b : F) ≤ 1 →
              (coordinateRepresentation W i b f).val a =
                ∑ η ∈ Y i, η b * (A i η f).val a) →
      ∃ X : Finset (Torus F n → ℂ), (∀ χ ∈ X, IsFiniteFunction T χ) ∧
        ∀ f : W.toSubmodule,
          ∃ Φ : (Torus F n → ℂ) → HarmonicAnalysis.SchwartzBruhat (Fin n → F),
            ∀ a : Torus F n,
              f.val a = ∑ χ ∈ X, Φ χ (fun i => (a i : F)) * χ a

end Langlands.AllField.Whittaker
