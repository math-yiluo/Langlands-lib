import Langlands.Representation.Whittaker.JPSDecompositionStatement
import Langlands.AllField.Representation.Whittaker.JPSFunctionSpace
/-!
# JPS function-space decomposition

The full conclusion of JPS (1979), Lemma (2.2.1), for the actual function spaces
and coordinate-germ quotients of `Langlands.Whittaker.JPSFunctionSpace`. This is
a proposition definition, not a proof.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding JPSDecompositionStatement
open Langlands.AllField.Whittaker

open scoped BigOperators

open Langlands.Whittaker.JPSFunctionSpace hiding CoordinateGerm FunctionSpace HasCoordinateUpperSupport HasFiniteCoordinateOperatorSpan HasFiniteOperatorSpans IsFiniteFunction IsLocallyConstantSpace Torus VanishesNearCoordinateZero coordinateEmbedding coordinateEmbedding_apply coordinateEmbedding_same coordinateRepresentation coordinateRepresentation_apply coordinateVanishing germMap germMap_eq_zero_iff germMap_surjective germRepresentation germRepresentation_apply_mk mul_coordinateEmbedding sigma sigma_apply_mk translate_apply vanishesNearCoordinateZero_add vanishesNearCoordinateZero_smul vanishesNearCoordinateZero_translate vanishesNearCoordinateZero_zero
open Langlands.AllField.Whittaker.JPSFunctionSpace

universe uF

/-- JPS (1979), Lemma (2.2.1): let `W` be a translation-stable space of locally
constant functions on `H = (Fˣ)ⁿ`, each vanishing when one coordinate is large,
uniformly in the others, such that every coordinate action `σ_i` on the actual
quotient `W / W_i` spans a finite-dimensional operator space. Then one finite set
`X` of finite functions on `H`, chosen before the function, expands every `f` in
`W` with Schwartz–Bruhat coefficients on the whole additive space `Fⁿ`. -/
def JPSDecompositionStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (W : FunctionSpace F n),
      IsLocallyConstantSpace W T →
      HasCoordinateUpperSupport W T →
      HasFiniteOperatorSpans W T →
      ∃ X : Finset (Torus F n → ℂ), (∀ χ ∈ X, IsFiniteFunction T χ) ∧
        ∀ f : W.toSubmodule,
          ∃ Φ : (Torus F n → ℂ) → HarmonicAnalysis.SchwartzBruhat (Fin n → F),
            ∀ a : Torus F n,
              f.val a = ∑ χ ∈ X, Φ χ (fun i => (a i : F)) * χ a

end Langlands.AllField.Whittaker
