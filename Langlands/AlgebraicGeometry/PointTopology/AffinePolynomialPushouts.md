# Adjoining a polynomial variable as an algebra pushout

Author: Worker 105.

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Proposition 2.1 and its
uniqueness proof on printed page 2. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`polynomialOptionPushout R ι` is the actual cocone in `CommAlgCat R` for the
two coefficient maps from `R` to `MvPolynomial ι R` and to the polynomial
line `MvPolynomial Unit R`. Its vertex is `MvPolynomial (Option ι) R`.
The first map sends each old variable to the variable indexed by `some i`;
the second sends its sole variable to the variable indexed by `none`.
The two composites from `R` agree because both preserve coefficients.

`polynomialOptionPushoutIsColimit` constructs the full universal property.
For any target cocone, its universal algebra map evaluates the `some i`
variable at the image of the corresponding old variable and the `none`
variable at the image of the line variable. Polynomial algebra-map
extensionality proves both factorizations. Evaluating the two assumed
factorization equations on these variables proves uniqueness.

No finiteness or topology hypotheses enter this algebraic construction.
Its role is to derive finite affine-space topology from the fibre-product
axiom by adding one polynomial line at a time. That topological derivation,
the scheme bridge and the full assertion of Proposition 2.1 are separate
obligations.
