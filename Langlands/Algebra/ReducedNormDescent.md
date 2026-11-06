# Galois descent of the determinant polynomial

This internal helper starts with a finite Galois extension `L/K` and an actual
matrix chart for `L tensor_K A`. It constructs a polynomial over `K` for every
finite family of elements of `A`. The splitting extension and chart are still
inputs of this helper, to be supplied by the unconditional construction.

For an automorphism `sigma` of `L/K`, `galoisTwistChart` first applies
`sigma` inverse on the coefficient factor of the tensor product, then the
original chart, then `sigma` to every matrix coefficient. The two semilinear
twists cancel on scalars, so the result is again an `L`-algebra equivalence.
On elements `1 tensor a` from the base algebra, its value is coefficientwise
`sigma` of the original chart image. Coefficient extension of the determinant
polynomial therefore gives the polynomial of this new chart. Polynomial
chart independence proves that it equals the original polynomial.

`exists_polynomial_descent` applies the finite Galois fixed-element theorem
to each coefficient of any fixed polynomial. All coefficients are in the
image of `K`, hence the polynomial itself is in the image of coefficient
extension from `K`. `descendedPolynomial` chooses that preimage for the
determinant polynomial, and `descendedPolynomial_map` proves its defining
coefficient-extension identity. Injectivity of the field map proves uniqueness,
reflects homogeneity to the base field, and proves independence of the chosen
chart over the same splitting field. These are identities of polynomials,
not tests of equality on the field's points; finite and imperfect base fields
are allowed.

The source convention is Milne, *Algebraic Groups* (2022 corrected reprint),
Remark 24.25, printed p. 523 / PDF p. 534, registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The retained author errata of 2026-11-04 do not correct this passage. The
coefficientwise Galois proof here is the internal polynomial version of that
determinant descent argument. Independence of different splitting fields,
evaluation on arbitrary scalar algebras, and unconditional existence of a
finite Galois splitting chart remain later parts of the construction.
