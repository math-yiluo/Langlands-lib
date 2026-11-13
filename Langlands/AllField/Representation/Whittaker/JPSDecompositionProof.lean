import Langlands.Representation.Whittaker.JPSDecompositionProof
import Langlands.AllField.Representation.Whittaker.JPSDecompositionStatement
import Langlands.AllField.Representation.Whittaker.JPSDilationAssemblyProof
import Langlands.AllField.Representation.Whittaker.JPSUniformDilationProof
/-!
# Proof of the JPS function-space decomposition

The published uniform dilation theorem supplies each coordinate's finite family
before the function is chosen. The published assembly theorem then gives the
uniform finite family on the full torus with Schwartz–Bruhat coefficients.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding JPSBoundedDilationRecurrenceStatement JPSCoordinateUnitInvarianceStatement JPSDecompositionStatement JPSDilationAssemblyStatement JPSUniformDilationStatement jpsBoundedDilationRecurrence jpsCoordinateUnitInvariance jpsDecomposition jpsDilationAssembly jpsUniformDilation
open Langlands.AllField.Whittaker

open Langlands.Whittaker.JPSFunctionSpace hiding CoordinateGerm FunctionSpace HasCoordinateUpperSupport HasFiniteCoordinateOperatorSpan HasFiniteOperatorSpans IsFiniteFunction IsLocallyConstantSpace Torus VanishesNearCoordinateZero coordinateEmbedding coordinateEmbedding_apply coordinateEmbedding_same coordinateRepresentation coordinateRepresentation_apply coordinateVanishing germMap germMap_eq_zero_iff germMap_surjective germRepresentation germRepresentation_apply_mk mul_coordinateEmbedding sigma sigma_apply_mk translate_apply vanishesNearCoordinateZero_add vanishesNearCoordinateZero_smul vanishesNearCoordinateZero_translate vanishesNearCoordinateZero_zero
open Langlands.AllField.Whittaker.JPSFunctionSpace

universe uF

/-- JPS (1979), Lemma (2.2.1), with one finite family for the entire function
space and Schwartz–Bruhat coefficients on the whole additive space. -/
theorem jpsDecomposition : JPSDecompositionStatement.{uF} := by
  classical
  intro F _ T n W hloc hsupport hspan
  choose Y A hY hA hgerm hexpand using fun i : Fin n =>
    jpsUniformDilation F T n W i hloc (hspan i)
  exact jpsDilationAssembly F T n W Y A hloc hsupport hY hexpand

end Langlands.AllField.Whittaker
