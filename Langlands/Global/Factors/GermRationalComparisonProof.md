# Proof of germ-based rational comparison

Proof author: Worker 352. Worker 12 prepared the proof pair for this focused submission against the published target.

The theorem `Langlands.Global.FunctionalEquationComparison.germRationalComparison` proves the complete published `GermRationalComparisonStatement`. It imports that statement from `Langlands.Global.Factors.GermRationalComparisonStatement`; its only finite-comparison dependency is the statement interface, without `FiniteComparisonProof`.

The implemented proof takes the real bounds a and b from the two supplied `HasRationalContinuation` certificates and chooses c = max(a, b) + 1. Equality of the punctured germs at c gives a positive radius δ and equality throughout the punctured complex ball. The real open interval (c, c + δ) lies in that ball, avoids c, and remains in both right half-planes. The Lean proof verifies the ball condition using the isometry of the real embedding into the complex numbers.

The interval is infinite. For q > 1 its image under the spectral map t ↦ q^(-t) is infinite by `spectralPoint_ofReal_injective`. The two continuation certificates give nonvanishing of both reduced denominators at every point of that image. Their value identities, combined with germ equality, give equality of the rational evaluations. The proof concludes with `rationalFunction_eq_of_infinite_eval_eq`.

This is an internal derived consequence of the published germ-equality and rational-continuation interfaces, with the motivation and original-source provenance recorded in the statement's Markdown. It applies to arbitrary complex functions f and g; their meromorphy is unnecessary. Both continuation certificates, including denominator regularity on actual right half-planes, remain explicit hypotheses. The theorem identifies only the two supplied rational functions. It constructs no continuation, local factor, or nonzero factor and leaves the statement's arithmetic, automorphic, analytic, and factor-existence input obligations with their existing owners.
