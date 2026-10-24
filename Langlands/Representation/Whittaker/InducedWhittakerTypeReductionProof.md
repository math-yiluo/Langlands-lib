# Algebraic reduction from localized heredity to Whittaker type

Author: Worker 174.

The theorem `Langlands.inducedWhittakerTypeReduction` proves exactly the closed
proposition `Langlands.InducedWhittakerTypeReductionStatement.{uF,uV}`. Its only
premise is the full published `InducedLocalizationStatement` and its conclusion
is the unchanged `InducedWhittakerTypeStatement`, with independent field and
block-module universes.

This is an internal algebraic derivation from published interfaces. A private
lemma identifies the existence of a nonzero ambient vector that belongs to and
spans a submodule with dimension one of that submodule. It passes between ambient
vectors and submodule elements by their inclusions and subtype extensionality,
then applies `LinearAlgebra.nonzero_span_iff_finrank_one`.

The proof introduces precisely the field, canonical topology, total-rank
topological-group instance, block data and assumptions of both target
propositions. `Whittaker.mem_functionals_entrywiseCharacter_iff` rewrites the
original double-index matrix covariance conditions as membership in the actual
functional submodules, including any zero-rank blocks. The private lemma
converts the existential and scalar-uniqueness clauses to dimension one.
`Whittaker.functionalsLocalizationDualEquiv` identifies each functional submodule
with the full dual of its character quotient.

The published `LinearAlgebra.dual_finrank_one_iff` reflects dimension one from
each full dual to its underlying quotient without presupposing finite
dimensionality. The quotient equivalence supplied by the premise preserves
dimension. Finally, `LinearAlgebra.piTensor_finrank_one_iff` turns dimension one
of the finite tensor product into dimension one of every block quotient, and
the block functional equivalences reverse the translation.

The proof uses the dimension lemmas underlying `dualTensorOneDimensional`;
it does not identify the full tensor dual with a tensor product of full duals.
It does not prove geometric heredity, invoke irreducibility, or strengthen the
admissibility or finite-type hypotheses. The unconditional host theorem still
requires an independently proved `InducedLocalizationStatement`.
