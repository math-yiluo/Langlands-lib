# Chamber assembly from root-Levi height bounds

This internal derived auxiliary unit combines the published original-root
bound with finite simultaneous height minima and supplied actual positive
coordinates. Its chamber results explicitly assume the universal rank-one
arithmetic statement. They also require the positive-coordinate hypothesis.
Neither input is proved by this unit.

`PositiveRealTorus.HasUniformSimpleRootBound` means that one positive
nonnegative-real unit bounds every normalized simple-root character norm
on a supplied family of actual original-torus adelic points. Finiteness of
the actual simple-root set combines its individual character bounds into
one bound. Inversion gives a common weak lower bound. Empty simple-root
sets are allowed.

The minimal-Levi commutation lemma follows from the setup's equality of
that Levi with the whole-torus centralizer, on every test scheme. It applies
the resulting centrality inside the minimal Levi to actual adelic points
and then maps the equality into the ambient group.

For the fixed-setup chamber implication, enumerate the actual finite
simple-root set and choose, at each index, the maximal standard parabolic
obtained by deleting that root. Distinctness of the enumeration ensures
that its singleton root Levi lies in every preceding parabolic. Choose
exact parabolic eigenlines by the published Chevalley construction.
Simultaneous right minima are taken over the intersections of preceding
rational parabolics; the parabolics themselves need not be nested.

A positive constant depending on the given compact subgroup transfers all
these finite minimum inequalities through a left compact factor. Apply the
published original-root bound to the family of all torus points occurring
in minimal-Levi, torus, unipotent products satisfying these inequalities.
Here the minimal-Levi coordinate is intrinsically norm one; the whole
product is not assumed intrinsically norm one in any root Levi. The root
bound's arithmetic premise supplies the normalized rank-one height bound.
Finiteness gives one constant for all original simple roots.

For a norm-one point, minimize its inverse on the right by a rational point.
Use the supplied positive coordinates and the prescribed Iwasawa compact
to factor the inverse of that translate in unipotent, minimal-Levi,
positive-torus, compact order. Invert the product, remove the left compact
factor using the common comparison constant, and commute only the torus
and minimal-Levi images. The inverse torus point then belongs to the family
just bounded. Inversion and character pullback give the weak lower chamber
inequality for the original positive coordinate. The rational point acts
on the left and the compact factor remains in the originally supplied
subgroup.

The last theorem packages this argument as the implication from the
universal rank-one arithmetic and minimal-parabolic positive-coordinate
statements to `AdelicSiegelChamberReductionStatement`, at arbitrary universe.
This is auxiliary conditional progress, not an unconditional proof or
completion of that target. The provenance is the imported Library
constructions and group, order and finite-set arguments described above;
no additional external source or coverage theorem is assumed.
