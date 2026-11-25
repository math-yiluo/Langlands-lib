# Intrinsic cyclic cutoffs in nonnegative polynomial coordinates

This derived module gives a direct intrinsic-cutoff criterion for the full
coordinate algebra of a corepresented group over an arbitrary commutative ring.
Unlike a presentation of the first positive cutoff, it permits zero-weight
variables in the original algebra.

`NonnegativeCyclicCoordinates` records a finite set of homogeneous algebra
generators, with weights w(i) times a character a, where w(i) are natural numbers.
Every generator is required to vanish at the identity, and polynomial evaluation
in these generators is surjective. No field, reducedness, smoothness, or algebraic
independence assumption is used. The record is presentation data, not an existence
theorem.

For a nonzero a and a positive cutoff r, `mem_iff` proves that a point over any
base algebra belongs to the intrinsic weight subgroup for the cyclic tail
{n*a : n >= r and n > 0} exactly when all generators of weight less than r vanish
at that point. This includes the generators of weight zero.

The proof works monomial by monomial. A monomial in the generators is homogeneous
of its total natural weight times a. The nonzero character makes the natural
multiple unique. If that character is outside the cutoff and the monomial is
nonconstant, one of its factors has weight less than r, so both its value at the
point and its augmentation vanish. Constant monomials have identical values
under the point and augmentation maps. Additivity and surjectivity complete the
proof. This avoids a polynomial-coordinate existence theorem or any extension
of scalars to a field.

`low_coordinates_conjugate` combines this criterion with the published arbitrary-
ring intrinsic conjugation theorem: a conjugator whose twisted orbit is constant
preserves every one of these coordinate cutoffs. Relating the data to a particular
root chart and proving invariance under changing maximal tori are separate steps
of the construction of finite vector-bundle filtrations for supplied relative radicals.
