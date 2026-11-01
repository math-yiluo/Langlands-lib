import Langlands.Representation.Whittaker.JPSDecompositionStatement
import Langlands.Representation.Whittaker.JPSUniformDilationProof
import Langlands.Representation.Whittaker.JPSDilationAssemblyProof

/-!
# Proof of the JPS function-space decomposition

The published uniform dilation theorem supplies each coordinate's finite family
before the function is chosen. The published assembly theorem then gives the
uniform finite family on the full torus with Schwartz–Bruhat coefficients.
-/

namespace Langlands.Whittaker

open JPSFunctionSpace

universe uF

/-- JPS (1979), Lemma (2.2.1), with one finite family for the entire function
space and Schwartz–Bruhat coefficients on the whole additive space. -/
theorem jpsDecomposition : JPSDecompositionStatement.{uF} := by
  classical
  intro p _ F T n W hloc hsupport hspan
  choose Y A hY hA hgerm hexpand using fun i : Fin n =>
    jpsUniformDilation p F T n W i hloc (hspan i)
  exact jpsDilationAssembly p F T n W Y A hloc hsupport hY hexpand

end Langlands.Whittaker
