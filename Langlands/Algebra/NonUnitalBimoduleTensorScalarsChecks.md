# Checks for compatible tensor residual actions

Worker 321 authored this companion to
`Langlands.Algebra.NonUnitalBimoduleTensorScalars`, with its construction by
Worker 185. It checks the internal adapter's exact interfaces and named
structures; the mathematical provenance and proof description are in the core
module's Markdown. No additional source theorem is asserted here.

The three complete unapplied assignments have the form `example : ∀ …, T :=
@name`. They check `linearEnd`, the actual nonunital algebra homomorphism
`action`, and `recoveredModule_eq` without first applying any arguments. The
compatibility input is written directly using
`NondegenerateScalars.module k hR.op hRX`, rather than an inferred module on X.
The comparison specifies the exact intrinsic nondegeneracy proof
`NondegenerateTensorFunctor.isNondegenerate hS hX hSX Y` and the exact tensor
module `NondegenerateTensorScalars.module k R X Y hR hY`.

Each assignment is checked with five independent universe variables, then with
closed patterns `(uk,uS,uR,uX,uY) = (0,1,2,3,4)` and `(4,3,2,1,0)`.
Thus no two of the five universes need coincide, in either ordering. The
signatures contain no coefficient module on either factor, no prior module on
the tensor, and no output compatibility or Module-equality input. The fixed-s
linear refinement has the stronger one-sided interface of the core: it needs
neither coefficients on S nor the right nondegeneracy of X.

The competing-structure section places arbitrary `Module k X`, `Module k Y`,
`Module k (Tensor R X Y)`, and original S-action instances on the tensor in
scope. It then explicitly pins MX to `NondegenerateScalars.module k hR.op hRX`,
MY to `NondegenerateScalars.module k hR hY`, MT to the published tensor
coefficient module, and HS to `NonUnitalBimoduleTensor.leftModule hX Y`.
Definitional checks identify these selected structures. Further checks use the
explicit MX compatibility to obtain both output compatibility classes and their
all-tensor laws, the actual pure formula, the whole action round trip, and the
Module equality. The two coefficient pure-tensor formulas pin both factor
modules as well as MT.

For the regular integer case, the original left and right actions are exactly
`NonUnitalModule.regular ℤ` and `NonUnitalModule.rightRegular ℤ`. The published
regular nondegeneracy lemmas provide the input proofs. Uniqueness of integer
modules identifies the recovered coefficients with the ordinary integer
multiplication, proving the required input compatibility. The actual bundled
action of 2 sends `tmul 1 1` to `tmul 2 1`, and the explicitly installed HS
has the same formula. The original balanced lift of `(x,y) ↦ x*y` sends
`tmul 2 1` to 2, so that output tensor is nonzero. This verifies a nonzero
actual example, not merely an identity on a subsingleton carrier.

The generic signatures impose no nontriviality, unit-action or dimension
condition. In particular they retain the zero and subsingleton cases admitted
by the core hypotheses. Zero actions on nonzero carriers are not asserted to be
nondegenerate. These are elaboration and kernel checks; independent semantic
review and publication remain separate requirements.
