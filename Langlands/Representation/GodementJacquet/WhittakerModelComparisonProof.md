# Proof of the matrix-coefficient versus Whittaker comparison on the coefficient model

Module `Langlands.Representation.GodementJacquet.WhittakerModelComparisonProof`.
Authors: Worker 261 and Worker 249.

This module proves the closed proposition
`Langlands.GodementJacquet.WhittakerModelComparisonStatement.{uF,uV}` as the
theorem `Langlands.GodementJacquet.whittakerModelComparison`, with no premises.

## Proof

The theorem is the conditional theorem
`Langlands.GodementJacquet.WhittakerTorus.Padic.whittakerModelComparison_of_asymptotics`
(module `WhittakerModelRationality`) applied to two published proofs:

- `Langlands.whittakerTypeAsymptotic : WhittakerTypeAsymptoticStatement`, the
  torus expansion of JPS (1979), Proposition (2.2) and Remark (2.2.5);
- `Langlands.RankinSelberg.finiteFunctionMellin : FiniteFunctionMellinStatement`,
  the Mellin transforms of finite functions times Schwartz–Bruhat functions.

The conditional theorem composes `modelWhittakerRationality` with the published
`GodementJacquet.whittakerModelComparison_of_rationality` (module
`WhittakerModelInclusion`). That theorem proves the equality by `le_antisymm`
from two inclusions.

1. `I₃ ⊆ I₂` (`Padic.jpssI3_le_jpssI2`, in the published Library module
   `WhittakerAveraging`, built on the published `LeftAveraging`). Every
   Whittaker integral on the model is a matrix-coefficient integral, with no
   analytic hypothesis.
2. `I₂ ⊆ I₃` (`Padic.jpssI2_le_jpssI3_of_rationality`, in the published
   module `WhittakerModelInclusion`). This half assumes
   `ModelWhittakerRationalityStatement`: every full-matrix Whittaker integral on
   the model converges on a right half-plane and has a rational continuation.
   A smooth functional on the admissible model is a finite combination of point
   averages over a compact open subgroup. A conjugation change of variables then
   turns each matrix-coefficient integral into a finite sum of Whittaker
   integrals.

`ModelWhittakerRationalityStatement` is proved from the two published inputs as
`WhittakerTorus.Padic.modelWhittakerRationality` (module
`WhittakerModelRationality`). The torus expansion is
transported to the coefficient model by the published `modelAsymptoticTransfer`.
The full-group Iwasawa integration formula (`RankinSelberg.IwasawaHaarIntegration`)
reduces each integral to a finite sum over `K` cosets of torus integrals
(`WhittakerCosetSum`, `WhittakerIwasawaReduction`). Their convergence
(`WhittakerMatrixConvergence`, with the volume bound of
`RankinSelberg.UnipotentDiagonalVolume`) and rationality
(`WhittakerMatrixRationality`, through `WhittakerTorusMellin` and
`WhittakerSliceSchwartz`) follow from `FiniteFunctionMellinStatement`.

## Source and provenance

JPSS (1983), *Rankin–Selberg convolutions*, Section (5.2), printed 420–421.
That section asserts the convergence and rationality of the full-matrix
integrals for representations of Whittaker type. It completes results of JPS
(1979), *Automorphic forms on GL(3) I*, whose Proposition (3.1), printed
185–186, treats irreducible generic representations. The Lean route differs
from the source as explained in the Markdown of `WhittakerModelInclusion`,
`WhittakerIwasawaReduction` and `WhittakerModelRationality`.
