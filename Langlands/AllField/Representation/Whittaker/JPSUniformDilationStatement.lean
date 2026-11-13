import Langlands.Representation.Whittaker.JPSUniformDilationStatement
import Langlands.AllField.Representation.Whittaker.JPSFunctionSpace
/-!
# Uniform small-coordinate dilation for actual JPS function spaces

The small-coordinate dilation step in the proof of JPS (1979), Lemma (2.2.1),
for the actual function spaces and coordinate-germ quotients of
`Langlands.Whittaker.JPSFunctionSpace`. This module defines a proposition only.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding JPSUniformDilationStatement
open Langlands.AllField.Whittaker

open Langlands.Whittaker.JPSFunctionSpace hiding CoordinateGerm FunctionSpace HasCoordinateUpperSupport HasFiniteCoordinateOperatorSpan HasFiniteOperatorSpans IsFiniteFunction IsLocallyConstantSpace Torus VanishesNearCoordinateZero coordinateEmbedding coordinateEmbedding_apply coordinateEmbedding_same coordinateRepresentation coordinateRepresentation_apply coordinateVanishing germMap germMap_eq_zero_iff germMap_surjective germRepresentation germRepresentation_apply_mk mul_coordinateEmbedding sigma sigma_apply_mk translate_apply vanishesNearCoordinateZero_add vanishesNearCoordinateZero_smul vanishesNearCoordinateZero_translate vanishesNearCoordinateZero_zero
open Langlands.AllField.Whittaker.JPSFunctionSpace

universe uF

/-- JPS (1979), proof of Lemma (2.2.1): from local constancy and a finite
coordinate operator span alone, one finite set `Y` of finite functions on `Fˣ`
and one operator family `A` in the span of the bounded coordinate dilations
`ρ_i(b)`, `|b| ≤ 1`, both chosen before every function, expand the action
`σ_i(b)` on the actual germ quotient for every `b`. For each `f`, one positive
threshold, chosen before the whole torus tuple and every `b` with `|b| ≤ 1`,
makes the expansion of `ρ_i(b) f` hold pointwise below it. -/
def JPSUniformDilationStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
      IsLocallyConstantSpace W T →
      HasFiniteCoordinateOperatorSpan W T i →
      ∃ (Y : Finset (Fˣ → ℂ))
        (A : (Fˣ → ℂ) → Module.End ℂ W.toSubmodule),
        (∀ η ∈ Y, Continuous η ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : Fˣ => fun a : Fˣ => η (b * a)))) ∧
        (∀ η ∈ Y, A η ∈ Submodule.span ℂ {B : Module.End ℂ W.toSubmodule |
          ∃ b : Fˣ, T.normalizedAbs (b : F) ≤ 1 ∧
            coordinateRepresentation W i b = B}) ∧
        (∀ (b : Fˣ) (f : W.toSubmodule),
          sigma W T i b (germMap W T i f) =
            germMap W T i (∑ η ∈ Y, η b • A η f)) ∧
        ∀ f : W.toSubmodule,
          ∃ ε : ℝ, 0 < ε ∧
            ∀ a : Torus F n,
              T.normalizedAbs (a i : F) < ε →
              ∀ b : Fˣ, T.normalizedAbs (b : F) ≤ 1 →
                (coordinateRepresentation W i b f).val a =
                  ∑ η ∈ Y, η b * (A η f).val a

end Langlands.AllField.Whittaker
