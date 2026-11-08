# The actual minuscule sum and its full-group spherical eigenidentity

This internal unit defines the finite minuscule right-translation operator on
actual functions on `GL_(n+1)`, with values in any commutative semiring. It is
linear over that semiring. The operator sums the values at `g * labelledRep`.

With integral, distinct and complete residue lifts, the operator preserves right
invariance under the integral subgroup. For each integral matrix, left
multiplication sends each labelled representative to the right coset of a
unique labelled representative. Existence follows from the minuscule double
coset decomposition; uniqueness gives injectivity of the index map, and
finiteness gives bijectivity. Reindexing the finite sum proves invariance.

For the actual spherical Laurent polynomial, left unipotent equivariance is
inherited term by term. Evaluation at every tuple of complex units turns the
sum into a complex equivariant, right integral-invariant function. Assuming
the character is nontrivial on the first inverse-uniformizer layer of each
adjacent root, the existing vanishing theorem makes this function zero at
nondominant torus elements. Injectivity of Laurent evaluations gives the same
vanishing in the actual symmetric Laurent algebra.

The previously proved dominant-torus minuscule recurrence therefore extends
to every torus element. Iwasawa decomposition, right integral invariance and
left unipotent equivariance extend it to every group element. The eigenvalue
is the actual symmetric Laurent polynomial
`sqrt(q)^(k * (n + 1 - k)) * e_k`.

The field and valuation are arbitrary subject to a supplied
`IsUniformizingElement v ϖ`: `v(ϖ) < 1` and every nonzero field valuation is an
integer power of `v(ϖ)`. Its integral ring must admit the chosen finite
complete and distinct residue lifts of cardinality `q > 0`. The integral
character triviality and adjacent-root nontriviality hypotheses are explicit.
No integrated numerator identity, universal finite support, full numerator
ideal, essential vector, factor comparison or conductor conclusion is proved
or assumed here. The provenance is the implemented internal deduction from
the existing actual coset, nondominant vanishing, Pieri and Iwasawa results.
