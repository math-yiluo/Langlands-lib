# Nonvanishing of coefficient maps after precomposition

Author: Worker 181, as a component of the joint task with Worker 654 on
`TwoBlockModelGenericSocleOccurrenceStatement`.

This internal algebraic module uses the actual coefficient maps from
`Whittaker.Algebraic` and pullback of equivariant functionals from
`Whittaker.Transport`. It permits any commutative coefficient ring, any group,
any subgroup and unit-valued character, and independent universes for the ring,
group, and two representation carriers. No smoothness or irreducibility is
assumed.

`coefficientMap_comp_range_ne_bot` proves that the composite of an intertwiner
`j : rho → sigma` with the coefficient map of an equivariant functional `ell`
has nonzero range whenever the functional pulled back along `j` is nonzero.
If that range were zero, every coefficient would be the zero function.
Evaluation at the identity, using `sigma(1) = id`, would force the pulled-back
functional to vanish.

`coefficientMapCompToSubrepresentation` constructs the composite coefficient
map with codomain restricted to an actual invariant subspace `M` containing
the coefficient image of `ell`. Its equivariance follows from equivariance of
the composite. `coefficientMapCompToSubrepresentation_range_ne_bot` transfers
the preceding nonvanishing argument through the injective inclusion of `M`
into the full equivariant function space.

The coefficient convention is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), Section 2.1, printed page 386, equation
(3): `W(g) = ell(sigma(g)v)`. The result above is an internal direct algebraic
consequence, used to supply the nonzero invariant image in the constituent
argument of Section 5.4, printed page 423 between equations (3) and (4).
Worker 181 visually read printed pages 385–387 and 423 from registered source
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
A bounded search of project and current Library notes and the literature index
found no registered source-specific JPSS errata.

These lemmas construct no socle, induction comparison, or analytic factor.
They are one algebraic component of the separate occurrence proof.
