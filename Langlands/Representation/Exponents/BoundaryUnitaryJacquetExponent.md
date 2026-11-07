# Actual unitary outer exponents from a supplied boundary face

This derived internal construction joins the root-support and actual exponent
projection arguments used toward the converse direction of Renard VII.2.4.
The geometric field universe and representation carrier universe are independent.
All parabolic, Levi, matching radical and split-component maps are the original
supplied maps. Nesting and the inner intersection are equalities or inclusions
of subgroup functors on every test scheme, and the actual inner Levi is the
same common Levi as the fine ambient parabolic.

A normalized fine Jacquet exponent of a tempered source is supplied, together
with its nonnegative real parameter in a compatible fine presentation and a
compatible outer presentation. Its nonnegative coefficient support enlarges
the original selected-root index as in `ParabolicBoundaryRootSupport`. Assume
this constructed index lies in the actual simple-root face of the supplied
outer Levi. The real parameter then restricts to zero on the original outer
split component.

`boundaryUnitaryJacquetExponent` returns an actual character in the published
unitary exponent set of the original outer Jacquet module. Its underlying
character is the given fine character composed with the rational-point map of
the constructed intermediate split-component factor. This factor is derived
from the original compatible fine presentation and centrality of the outer
split component; no arbitrary point homomorphism is assumed. Normalized
transitivity, outer Jacquet admissibility from temperedness and central exponent
restriction prove that this character occurs in the actual outer Jacquet
module. Naturality of the normalized real part and the root-support vanishing
result prove its real parameter is zero. The final theorem uses this witness
to prove the outer unitary Jacquet part is nonzero.

The nonnegative cone premise is automatically available from temperedness for
any supplied fine presentation. Failure of strict positivity is not needed for
the construction itself. When strict positivity fails, the root-support module
separately proves that the constructed index is proper. This module does not
construct an outer parabolic realizing that index, prove the supplied outer
parabolic proper, or prove Casselman's criterion or the VII.2.4 equivalence.
