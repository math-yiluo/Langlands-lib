# Multivariable adelic Schwartz Mellin convergence

This internal helper combines `AdelicSchwartzProductMajorant` with the
rank-one Haar convergence theorem of `AdelicSchwartzMellinHaar`.
Its hypotheses include compactness of the additive adelic quotient, as
required to obtain domination and continuity of the rank-one
Schwartz–Bruhat majorant.

`ideleTorusMellinKernel` names the nonnegative function on actual ideles
obtained by evaluating the row function on their underlying adeles, taking
its extended norm, and multiplying by the product of the full idele norms
to the prescribed real coordinate powers. No quotient or choice of
representatives occurs in this definition.

First, `lintegral_fin_prod_eq_prod` proves Tonelli's formula for a product
of measurable nonnegative functions of separate finite coordinates.
The proof splits off the first coordinate by a measure-preserving
equivalence and applies the binary product formula inductively.

The rank-one Mellin kernel is measurable: the test function is continuous,
the idele norm is continuous and strictly positive, and a fixed real
power is continuous on that positive range.

For a dominated function on rows of positive length, choose the common
rank-one Schwartz–Bruhat product majorant. After multiplying by the
nonnegative powers of the idele norms, its product still bounds the
original kernel. Tonelli's formula writes the integral of that product
as the product of its rank-one integrals. Each is finite when its
coordinate exponent is greater than `3`, independently of the chosen
coordinate Haar normalizations. The original function itself need not
be continuous or measurable, since monotonicity of the lower integral
suffices for the final bound.

Haar uniqueness then compares any Haar measure on the whole finite idele
torus with the product of chosen rank-one Haar measures by a positive
finite scalar. Thus convergence holds for every Haar normalization on
that torus. The final corollary applies this result to any
Schwartz–Bruhat test function. The named-kernel theorem restates the
dominated-function conclusion for `ideleTorusMellinKernel`. This module
asserts no Whittaker quotient integration formula or whole-group gauge
existence result.
