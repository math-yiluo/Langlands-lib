# Finite-length uniformization of coefficient growth

`Langlands.Plancherel.FiniteLengthCoefficientGrowthUniformizationStatement`
isolates an internal algebraic step toward the finite-length assertion of
moderate coefficient growth. It quantifies over a topological group `G` with
`CompactOpenCofinal G`, an arbitrary function `H : G → ℝ` with `H g ≥ 1` and
`H (g * h) ≤ H g * H h`, and an admissible finite-length smooth complex
representation `π`. The group and carrier universes are independent.

The premise supplies an estimate for each vector `v` and smooth dual functional
`φ`, with both a natural exponent and a positive constant depending on the pair:

`∀ v φ, ∃ d c, 0 < c ∧ ∀ g, ‖φ (π(g) v)‖ ≤ c * H(g)^d`.

The conclusion moves the exponent outside both coefficient arguments:

`∃ d, ∀ v φ, ∃ c, 0 < c ∧ ∀ g, ‖φ (π(g) v)‖ ≤ c * H(g)^d`.

The positive constant may still depend on `v` and `φ`. The height has no
continuity, properness, symmetry, or normalization-at-one hypothesis; these
properties are unnecessary for this finite-generation step. Compact-open
cofinality and admissibility allow the published smooth-contragredient
finite-length theorem to apply. Finite length then implies finite generation
over the complex group algebra for both `π` and its smooth dual.

The internal provenance is the finite-generation argument: for a fixed vector,
degree-bounded smooth functionals form an ascending family of submodules for the
contragredient group-algebra action. The coefficientwise premise exhausts the
smooth dual, so finite generation supplies one degree for that vector. Vectors
whose coefficients all have a fixed degree bound likewise form ascending
group-algebra submodules. A second finite-generation step supplies a single
degree for all vectors. Submultiplicativity controls both left and right
translates; the lower bound by one makes degree bounds monotone.

This pair states that implication; it does not prove coefficientwise growth,
compact-open cofinality for any particular group, or the analytic convergence
and rationality conclusions of `ConditionalParabolicIntertwiningStatement`.
It imposes no new premise on that unchanged final target. Applying this helper
to actual rational-point matrix norms requires proving its displayed premises.
