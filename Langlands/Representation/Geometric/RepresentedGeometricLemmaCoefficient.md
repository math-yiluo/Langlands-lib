# The normalized coefficient on the target intersection

This internal construction is derived from the represented geometric-lemma
intersection datum, the literal target-intersection maps, and unimodularity
of rational points of a unipotent radical over a nonarchimedean local field.
The coefficient carrier has its own universe parameter, with no dimension or
finiteness restriction.

For the original source parabolic \(P=MN\), the normalized inducing action
on a smooth representation of \(M\) is
\(\delta_P^{1/2}(p)\sigma(\operatorname{pr}_M(p))\).
`leviInducingFunctor_radical_apply` proves that every element of \(N\)
acts trivially: the projection is the identity element and the half modulus
is one by radical unimodularity.

`targetIntersectionCoefficientFunctor` pulls this actual coefficient action
to \(L\cap z^{-1}Pz\) through conjugation by \(z\).
`commonLeviCoefficientFunctor` restricts it further to
\(L\cap z^{-1}Mz\).
The target intersection radical \(L\cap z^{-1}Nz\) acts trivially because
conjugation carries it into \(N\).

The equality `targetIntersectionCoefficient_eq_comp_projection` proves that
the coefficient is inflated from its common-Levi restriction along the actual
target-intersection Levi projection. The proof factors each intersection
element into its projected Levi factor and a radical element, then removes
the trivial radical action. `targetIntersectionCoefficientInflationIso`
packages this equality as a natural isomorphism, whose underlying linear map
at every coefficient is the identity.

This statement concerns the inducing coefficient restricted to the target
intersection. It does not compute the coinvariants of the full orbit piece,
the full stabilizer projection, or the distinct-radical modulus balance.
