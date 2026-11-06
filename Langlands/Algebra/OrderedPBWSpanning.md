# Spanning by ordered monomials in the actual enveloping algebra

Author: Worker 1431.

This internal unit proves the spanning clause for the published ordered finite-basis
PBW target. The field and Lie algebra have independent universes `u` and `v`.
The only mathematical inputs are a field, a Lie ring with a compatible Lie algebra
structure, and a basis `b : Module.Basis (Fin n) k L`. The result includes every
field characteristic and `n = 0`.

`basisWord b w` evaluates a list of basis indices by multiplying their images under
Mathlib's actual generator map into `UniversalEnvelopingAlgebra k L`. The empty
word evaluates to one, a cons evaluates by left multiplication, and concatenation
evaluates by multiplication. `generator_eq_sum_basis` applies linearity of the
actual generator map to `b.sum_repr`.

`basisWord_adjacent_swap` proves the local reordering identity in the actual
quotient. The Lie-homomorphism property of the generator map identifies the image
of the bracket with the difference of the two products. Expanding the bracket in
the supplied basis and multiplying by the evaluated prefix and suffix gives the
swapped word plus the finite sum of shorter bracket words. This uses the
alternating Lie-ring structure already assumed by Mathlib, without division by
two or any assumption on the characteristic.

`basisWord_mem_ordered_span` applies well-founded induction in the shortlex order
on finite-index words. A nondecreasing word is its exponent word, so its
evaluation equals the published `orderedPBWMonomial` by `OrderedPBWWords`.
Otherwise, an adjacent inversion can be swapped: the swapped word decreases
lexicographically at equal length, and each bracket word has smaller length.
The induction hypotheses and closure of a submodule under sums and scalar
multiplication put the original word in the ordered-monomial span.

`basisWord_span_mul` uses two-variable span induction. Products of basis words
are evaluations of concatenations, and bilinearity extends membership to the
full span. `span_basisWord_eq_top` lifts an arbitrary element of the actual
universal enveloping algebra to the tensor algebra by quotient surjectivity.
Tensor-algebra induction then puts its image in the basis-word span: scalars
are multiples of the empty word, a Lie generator is its basis expansion, and
the span is closed under sums and products. Finally, `orderedPBWMonomial_span`
compares the two spans using the exponent-word evaluation identity in one
direction and shortlex reduction in the other.

The unit proves full span in the actual quotient; it does not establish linear
independence or a unique normal form. The argument is internal elementary
infrastructure derived directly from Mathlib's tensor-algebra quotient and the
published monomial construction. No additional literature assertion is assumed.
The full PBW theorem remains a separate proof obligation of this task.
