# Exhaustion by finitely generated invariant submodules

This is an internal algebraic construction by Worker 288, used in the passage
from finitely generated inputs to arbitrary smooth inputs for support
preservation. It has independent coefficient, group and carrier universes and
retains the original carrier universe for all subrepresentations.

`SmoothRep.finiteSpanSubrepresentation A s` is the actual invariant submodule
corresponding to the span of the finite set `s` in the group-algebra module
`A.representation.asModule`. The span is over `MonoidAlgebra R G`. It is not
asserted to have finite dimension over `R` or finite length.

`finiteSpanSubrepresentation_finite` identifies the group-algebra module of the
smooth subrepresentation with that span by the restricted inclusion. The
restricted map is bijective. Mathlib's `Module.Finite.span_of_finite` and
`Module.Finite.equiv` then give finite generation.

`finiteSpanSubrepresentation_mono` is span monotonicity.
`finiteSpanSubrepresentation_directed` uses the union of two finite sets as an
upper bound. `iSup_finiteSpanSubrepresentation` puts each vector into the span of
its singleton, proving that the actual invariant sum of these submodules is
the whole representation, including the zero representation.

`image_isQuotient` restricts the codomain of an actual intertwiner to its
invariant range. The resulting intertwiner is surjective.

These are derived algebraic facts. Their proof bodies use group-algebra spans,
actual intertwiners and module finiteness. They invoke no classification,
character independence, geometric lemma or adjointness theorem.
