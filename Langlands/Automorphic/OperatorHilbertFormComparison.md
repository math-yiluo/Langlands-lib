# Hilbert extensions for independently supplied positive forms

This internal prerequisite compares the Hilbert completions of two actual operator
realizations equipped with independently supplied full invariant positive forms.
The number field has an arbitrary universe, the rank is arbitrary, the source
realization is irreducible and jointly admissible, and a full operator equivalence
from the source realization to the target realization is supplied. No existence
of either positive form is assumed beyond supplying it.

`OperatorUnitaryFormCore.HilbertFormComparison` is the explicit Prop-valued
predicate for the extension, positive inner-product ratio and the two completed
action covariance identities. `OperatorHilbertFormComparisonStatement` asserts that the original equivalence
extends to a continuous complex-linear equivalence between the two actual Hilbert
completions. The extension agrees with the original equivalence under the dense
canonical embeddings. It multiplies inner products by one strictly positive real
scalar, and intertwines both completed finite translations and completed standard
infinite compact translations on these same Hilbert spaces.
`operatorHilbertFormComparison` proves this statement.

The proof pulls the target form back along the supplied full equivalence and uses
`OperatorUnitaryFormComparison` to compare that pullback with the independently
supplied source form. Their positive scale factor gives the exact norm ratio
`sqrt a` on the dense embedded carrier and the reciprocal ratio for the inverse.
Mathlib's `LinearEquiv.extend` therefore extends the original equivalence using
these two bounds. Density gives uniqueness, extends the inner-product identity,
and extends the finite and compact covariance identities. The generic completion construction, norm ratios and uniqueness are in
`Langlands.Representation.Unitary.CompletionSimilarity`. This module exposes
the actual covariance and pullback-comparison results, including covariance for any further operators that
already have continuous extensions with the prescribed values on the dense
carriers.

The provenance is internal composition of `OperatorUnitaryFormComparison`,
`OperatorUnitaryForm`, `OperatorHilbertCompletion`, `CompletionSimilarity` and Mathlib's extension of a
bounded linear equivalence along dense embeddings. The earlier
`OperatorHilbertIntertwiner.completedEquivalence` uses the form pulled back from
the target; the present result permits both forms to have been chosen independently
and retains their scale factor. No external theorem is newly asserted.

The general covariance lemma requires continuous operator extensions as explicit
inputs. In particular the result does not assert bounded extensions of the real
Lie or enveloping-algebra operators, a full archimedean group action, a description
of Hilbert smooth vectors, or continuity of the actual Whittaker functional in a
smooth Hilbert topology. These remain separate obligations toward unconditional
cuspidal operator multiplicity one.
