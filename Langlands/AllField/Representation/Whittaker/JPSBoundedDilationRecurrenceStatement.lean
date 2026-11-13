import Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement
import Langlands.AllField.Representation.Whittaker.JPSFunctionSpace
/-!
# Uniform-region recurrence for powers of a bounded coordinate dilation

For an actual JPS function space with a finite coordinate operator span, the
powers of one bounded coordinate dilation satisfy one scalar linear recurrence
pointwise on a whole small-coordinate region. This module defines a proposition
only.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding JPSBoundedDilationRecurrenceStatement
open Langlands.AllField.Whittaker

open Langlands.Whittaker.JPSFunctionSpace hiding CoordinateGerm FunctionSpace HasCoordinateUpperSupport HasFiniteCoordinateOperatorSpan HasFiniteOperatorSpans IsFiniteFunction IsLocallyConstantSpace Torus VanishesNearCoordinateZero coordinateEmbedding coordinateEmbedding_apply coordinateEmbedding_same coordinateRepresentation coordinateRepresentation_apply coordinateVanishing germMap germMap_eq_zero_iff germMap_surjective germRepresentation germRepresentation_apply_mk mul_coordinateEmbedding sigma sigma_apply_mk translate_apply vanishesNearCoordinateZero_add vanishesNearCoordinateZero_smul vanishesNearCoordinateZero_translate vanishesNearCoordinateZero_zero
open Langlands.AllField.Whittaker.JPSFunctionSpace

universe uF

/-- Derived from the proof of JPS (1979), Lemma (2.2.1): if the actual coordinate
germ action `σ_i` has a finite-dimensional operator span, then for every unit `c`
with `|c| ≤ 1` there are one length `D` and one family of scalar coefficients
`d m j`, both chosen before every function, such that for each `f` one positive
threshold, chosen before every power `m` and the whole torus tuple, makes every
`ρ_i(c ^ m) f` equal to `∑ j < D, d m j • ρ_i(c ^ j) f` pointwise below it. -/
def JPSBoundedDilationRecurrenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
    HasFiniteCoordinateOperatorSpan W T i →
    ∀ c : Fˣ, T.normalizedAbs (c : F) ≤ 1 →
      ∃ (D : ℕ) (d : ℕ → Fin D → ℂ),
        ∀ f : W.toSubmodule,
          ∃ δ : ℝ, 0 < δ ∧
            ∀ (m : ℕ) (a : Torus F n),
              T.normalizedAbs (a i : F) < δ →
                (coordinateRepresentation W i (c ^ m) f).val a =
                  ∑ j : Fin D, d m j * (coordinateRepresentation W i (c ^ (j : ℕ)) f).val a

end Langlands.AllField.Whittaker
