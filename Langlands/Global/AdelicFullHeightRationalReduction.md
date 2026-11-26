# Rational representatives with control of full adelic height

`adelicFullHeightRationalReduction` proves
`AdelicFullHeightRationalReductionStatement`. For a connected reductive group
over a number field and a positive-dimensional closed matrix representation,
there is a fixed compact subset of the finite adelic points and a fixed
polynomial bound. Every adelic point has a rational left translate with
finite component in that compact set and full adelic height within the
polynomial bound in the original point's height.

The proof first removes a central factor whose finite component is the
identity and whose height is polynomially bounded. On the resulting
norm-one point, the finite-translate Siegel cover supplies a rational
translate which is a Siegel point times a member of a fixed finite set.
The compact finite components of the Siegel product and the finite set
give the desired compact set. For the height estimate, bound the height
of the Siegel point using its inverse rational translate, then multiply
by the bounds for the central factor and the finite translate.

The norm comparison on the Siegel product is the Library's polynomial
form of Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*
(1995), I.2.2 (vii), pp. 20–21. The full-height reduction is a consequence
of that comparison together with the adelic cover and central height
bound.
