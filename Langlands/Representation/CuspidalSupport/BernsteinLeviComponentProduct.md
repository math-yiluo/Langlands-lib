# Restriction on Bernstein component products for a standard Levi

For a represented standard Levi with presentation `D`,
`BernsteinLeviPresentation.componentProductHom` sends the product of
ambient Bernstein component rings to the corresponding product for the
standard family of the Levi. At a Levi inertial class, take its chosen
cuspidal datum and transport it to an ambient datum. The map on that
coordinate changes from the chosen ambient representative to the
transported datum, includes regular functions invariant under the
ambient component group among those invariant under the relative Weyl
subgroup, and transports back to the intrinsic Levi component ring.

`BernsteinLeviComponentProductStatement` asserts that the product map is
finite and gives its evaluation law. At a character of a chosen Levi
datum, evaluation after restriction gives the value of the ambient
tuple at the transported datum and character. The proof uses the
evaluation law for the inverse of the relative component equivalence.
The inclusion of invariant rings preserves the underlying regular
function, and the change of ambient representative agrees with
`componentProductOn` because both use the same ambient inertial class.

For finiteness, the intrinsic inertial-class embedding sends each fibre
over an ambient class injectively into the corresponding fibre of
`standardLeviInertialToAmbient`. This gives a common bound on the sizes
of the fibres. The uniform invariant-module bound supplies a common
number of generators for the relative invariant ring over the ambient
invariant ring at every coordinate. Transporting the generators and
their coefficients through the component equivalences preserves this
number. The product-module lemma combines these bounds into a finite
spanning family by assigning the coordinate generators to a bounded
set of positions in each fibre.

This is the component-ring form of pullback along Renard's Levi map
on inertial classes in VI.7.3, using the invariant rings of VI.7.1.
It supplies the finite algebra map used for the finiteness in VI.10.5.
The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition of 9 July 2026, printed pp. 180–181, 185,
and 213 (PDF pp. 186–187, 191, and 219), registered as
`renard-2026-representations-groupes-reductifs-padiques` with SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
