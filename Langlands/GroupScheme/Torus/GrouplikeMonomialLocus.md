# Monomial loci of finite-character grouplike families

This internal algebraic construction extends the Library's idempotent
identity-locus argument from endomorphisms of one character group to maps
between two arbitrary abelian character groups. It uses the published
coefficient description of grouplike elements and finite generation.

Let `B` be a commutative algebra over a commutative base ring, let `Λ`
and `Γ` be abelian groups, and let `s` be a multiplicative homomorphism
from `Multiplicative Λ` to the units of `B[Γ]`. Assume every value is
grouplike. For a supplied additive homomorphism `p : Λ →+ Γ`,
`HasIdempotentMonomialLocus s p` means that one idempotent of `B`
detects, after every coefficient-algebra map, whether the family becomes
the monomials with degrees prescribed by `p`.

If `Λ` is finitely generated, `exists_idempotent_monomial_locus` proves
this property. Choose a finite generating set of the multiplicative
source group and take the product of the coefficients at their proposed
degrees. These coefficients are idempotents. After a coefficient map,
the product is one precisely when each selected coefficient is one:
an idempotent dividing one is a unit and hence is one. The existing
grouplike coefficient criterion gives equality with each monomial.
Equality on the generating set gives equality of the full families.

Over a domain, each grouplike element has one nonzero coefficient,
which is one, and all remaining coefficients vanish.
`exists_monomial_specialization` therefore extracts an actual additive
character map from every coefficient specialization to a domain.
Multiplicativity of the specialized family gives additivity of the
extracted degrees by injectivity of the monomial basis.

Finally, `exists_idempotent_monomial_presentation` combines the two
arguments. For every domain specialization there is a character map
and an idempotent whose image at that specialization is one, such that
the same character map describes the family exactly on the locus where
the idempotent becomes one. The target character group may have torsion;
the source group need only be finitely generated.

This module is algebraic. It does not yet convert these idempotent loci
into open covers of schemes or prove a local presentation theorem for
arbitrary group-scheme morphisms.
