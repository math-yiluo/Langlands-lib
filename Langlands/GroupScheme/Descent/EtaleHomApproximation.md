# Etale approximation of completed homomorphisms

This derived construction applies finite-coefficient descent of
actual group homomorphisms and finite-order etale approximation.

Let `P` be a local ring satisfying `EtaleCompletionApproximation P`. Let
`C` and `D` be groups over `Spec P`, with `C` quasi-compact and
quasi-separated and `D` locally finitely presented. For an actual
homomorphism between their base changes to the maximal-ideal completion,
`exists_approximation` supplies an etale `P`-algebra `E`, a map from `E`
to the completion, and a homomorphism between the groups over `Spec E`.
Evaluation of the new homomorphism at the resulting residue-field point
is exactly evaluation of the original completed homomorphism. Evaluation
uses the canonical comparisons of actual base changes.

The proof descends the completed homomorphism to a finite coefficient
subalgebra of the completion. It approximates the inclusion of that
subalgebra to order one through an etale algebra. The resulting two
coefficient maps to the residue field coincide, and functoriality of
evaluation proves the exact equality of the special-fibre maps.

The approximation property is an explicit hypothesis. Neither a complete
lift nor its clopen immersion properties are asserted by this lemma.
