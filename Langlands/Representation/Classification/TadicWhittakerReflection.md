# Whittaker nondegeneracy of actual twisted and complementary products

Worker 1732. This is derived content obtained by composing the existing actual
determinant twist, its functional equivalence, and the full finite-product
nondegeneracy criterion. It adds no classification premise or literature
assertion.

For a finite p-adic field with compatible topology and a continuous nontrivial
unitary additive character, `segmentFactorFunctionalsEquiv` constructs a
complex-linear equivalence from the entire upper-character functional submodule
of a supplied smooth representation to that of its real determinant twist.
Both directions retain the underlying linear functional. Its corollary
`hasFunctional_segmentFactor_iff` says that a real
determinant twist of an actual smooth complex representation has a nonzero
upper-character functional exactly when the original representation does.
This holds in every natural rank, including zero, with independent field and
representation universes. The proof uses the existing all-rank
`TopLocalization.realPowerCharacter_upper` theorem that determinant real-power
characters are trivial on upper unipotents. It then applies the
existing `twistFunctionalEquiv`, which retains the underlying linear
functional in both directions. Nontriviality of the full functional submodule
is equivalent to existence of a nonzero functional.

`hasFunctional_twistedProduct_iff` applies the full finite-product criterion
to the actual twisted block family and then removes each factor's twist
using that equivalence. Its factors are precisely the original supplied
smooth representations, with carrier universe `max uF uV` and their supplied
block ranks. Empty rank-zero and singleton products are included.

`SpehDatum.hasFunctional_complementaryInduced_iff` applies this result to the
actual two-block product of opposite twists of the same supplied
representation `S`. The constant two-factor condition is equivalent to
nondegeneracy of `S`; the forward direction evaluates at index zero, and
the reverse direction uses the same functional-existence assertion at both
indices. This uses the actual `d.complementaryInduced S alpha` from
`TadicUnitaryStatement`, with no alternative induction model.

The last result needs only the raw positive-rank Speh datum and any real
`alpha`. It does not require `S` to be a Speh representation or `alpha` to lie
in the complementary interval. None of these assertions includes
irreducibility, admissibility, finite length, finite dimension or unitarity.
They concern nonzero functional existence. They do not prove higher-Speh
nongenericity, Tadic exhaustion, strict Hermitian parameters or the final
unitary-generic exhaustion theorem.
