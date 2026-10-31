# Canonical homogeneous components of the genuine symmetric algebra

This internal construction supplies degree projections on Mathlib's actual
`SymmetricAlgebra R M`. It uses an auxiliary polynomial variable: the universal
algebra map sends each generator to the monomial of degree one with that generator
as coefficient. Extracting the degree `d` coefficient defines `component`.
The construction is independent of a basis and uses arbitrary universes for the
commutative coefficient ring and its module.

`homogeneousSpan R M d` is the linear span of actual symmetric monomials whose
lists have exactly length `d`. Components belong to these spans, act by the
Kronecker formula on each span, and recover every tensor by a finite sum.
Products satisfy the ordinary antidiagonal convolution formula. Algebra maps
induced by linear maps commute with the projections.

For a field `R : Type` and an arbitrary-universe Lie algebra `L`, the final
namespace connects this construction to the published
`UniversalEnveloping.symmetricDegreeFiltration`. Membership in its degree `d`
piece is equivalent to vanishing of every component with index greater than `d`.
Such an element is the sum of its components with indices from zero through `d`.
These results hold in every characteristic and assume neither finite dimension
nor PBW injectivity.

The proofs use the universal property, polynomial coefficient identities and
linear-span induction. This is a derived algebraic prerequisite for controlling
degrees during the transfer from symmetric covariants to enveloping operators.
It does not assert finite central generation or the automorphic growth theorem.
