import Langlands.Representation.Whittaker.JPSCoordinateUnitInvarianceStatement
import Langlands.AllField.Representation.Whittaker.JPSFunctionSpace
/-!
# Uniform coordinate-unit invariance for actual JPS coordinate germs

An internal regularity and uniformity prerequisite for JPS (1979), Lemma (2.2.1).
This module defines a proposition only.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding JPSCoordinateUnitInvarianceStatement
open Langlands.AllField.Whittaker

open Langlands.Whittaker.JPSFunctionSpace hiding CoordinateGerm FunctionSpace HasCoordinateUpperSupport HasFiniteCoordinateOperatorSpan HasFiniteOperatorSpans IsFiniteFunction IsLocallyConstantSpace Torus VanishesNearCoordinateZero coordinateEmbedding coordinateEmbedding_apply coordinateEmbedding_same coordinateRepresentation coordinateRepresentation_apply coordinateVanishing germMap germMap_eq_zero_iff germMap_surjective germRepresentation germRepresentation_apply_mk mul_coordinateEmbedding sigma sigma_apply_mk translate_apply vanishesNearCoordinateZero_add vanishesNearCoordinateZero_smul vanishesNearCoordinateZero_translate vanishesNearCoordinateZero_zero
open Langlands.AllField.Whittaker.JPSFunctionSpace

universe uF

/-- Local constancy and finite coordinate operator span give one compact open
norm-one subgroup acting trivially on the actual coordinate-germ quotient.
For each representative, one positive coordinate threshold works for all torus
tuples and every element of that subgroup. This is an internal derived target. -/
def JPSCoordinateUnitInvarianceStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (W : FunctionSpace F n) (i : Fin n),
      IsLocallyConstantSpace W T →
      HasFiniteCoordinateOperatorSpan W T i →
      ∃ U : Subgroup Fˣ,
        IsOpen (U : Set Fˣ) ∧
        IsCompact (U : Set Fˣ) ∧
        (∀ u ∈ U, T.normalizedAbs (u : F) = 1) ∧
        (∀ u ∈ U, ∀ q : CoordinateGerm W T i, sigma W T i u q = q) ∧
        ∀ f : W.toSubmodule,
          ∃ ε : ℝ, 0 < ε ∧
            ∀ a : Torus F n,
              T.normalizedAbs (a i : F) < ε →
              ∀ u ∈ U, (coordinateRepresentation W i u f).val a = f.val a

end Langlands.AllField.Whittaker
