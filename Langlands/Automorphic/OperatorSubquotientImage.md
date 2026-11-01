# Actual presentations for images of whole-operator quotient maps

This internal derived construction starts with an actual automorphic
`OperatorSubquotient Q` and any complex-linear whole-operator intertwiner `L`
from its quotient representation into a supplied complex representation.
The number field has arbitrary universe, the matrix rank is any natural number,
and the target carrier has an independent universe. No topology, CM-field
hypothesis or character is required on the target.

`imagePresentation` keeps `Q.upper`, an actual invariant subspace of the
constructed automorphic function space. Its denominator is the kernel of
`L.comp Q.projection`, an actual invariant subspace of that same numerator.
Membership means exactly `L (Q.projection f) = 0`. This denominator contains
`Q.lower`, since the original canonical projection kills that denominator.

The published equivariant quotient lift constructs `imageProjection`, from
`Q` onto the new presentation. Its representative formula sends the class of
`f` to the class of the same numerator vector `f`. Surjectivity follows from
the new canonical projection's surjectivity. Its kernel is exactly `L.ker`,
as proved by passing to a numerator representative and applying both exact
projection-kernel formulas.

The same published lift constructs `imageInclusion`, from the new presentation
into the supplied target. On a numerator representative it applies `L` to the
original quotient class. Mathlib's `Submodule.ker_liftQ_eq_bot` proves
injectivity: the new denominator is precisely the kernel of the map being
lifted. The composition of this injective factor with `imageProjection` is
the original `L`. Its range is exactly `L.range`. These identities are proved
on representatives using the surjectivity of the canonical projections.

`imageRangeMap` restricts the injective factor to the genuine invariant
range of `L`, using the existing intertwiner range construction. The
factorization proves it is surjective, and injectivity is inherited from
`imageInclusion`. Mathlib's genuine intertwiner `ofBijective` constructs
`imageEquivRange`, a representation equivalence retaining every concrete
operator. Its underlying target vector is exactly `imageInclusion`, and
its composite with `imageProjection` is exactly `L`.

If the supplied `L` is surjective, the injective factor is also surjective.
`imageEquivOfSurjective` then identifies the new actual presentation with
the entire supplied target representation, again with the exact factorization
formula. When that target is another actual automorphic presentation,
`imagePresentation_isoClass_eq` gives equality in the published whole-operator
isomorphism-class quotient.

Provenance is internal: this is the first isomorphism construction on the
published actual numerator/denominator quotient, not a new identification with
automorphic literature. It directly reuses the published equivariant quotient
lift, the genuine intertwiner kernel and range, Mathlib's exact kernel theorem
for `Submodule.liftQ`, and genuine representation equivalences from bijective
intertwiners. The related `RepSubfunctor.quotientNatIsoOfSurjective` performs
a first-isomorphism construction for objectwise natural maps; this unit instead
constructs a fixed actual automorphic presentation for every supplied map out
of an existing actual quotient.

The construction assumes no nonzero vector, irreducibility, maximal denominator
or spectral existence. It supplies no embedding of the quotient into functions,
evaluation of quotient vectors or quotient topology. The arbitrary target is
supplied mathematical input; the result proves that its image, and its whole
carrier when the map is surjective, is represented by the explicitly constructed
actual automorphic quotient.
