# Actual triangular additive polynomial coordinate changes

This module realizes the triangular additive polynomial coordinate changes in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma B.1.7 and its proof, printed pp.563–564 (one-based PDF pp.589–590).
The all-characteristic and all-test formulation is derived from the displayed
polynomial formulas. It works over any field, including finite and imperfect
fields, without a characteristic assumption.

For a distinguished coordinate `j` and polynomials `q i`,
`polynomialShearValues` sends a tuple `x` to the tuple whose `j` entry is
`q j` evaluated at `x j` and whose other entries are `x i + q i(x j)`.
Coefficients are evaluated along an arbitrary ring homomorphism into an
arbitrary commutative ring. The coefficient, index and value universes are
independent. `eval₂_polynomialShear` identifies this operation with evaluation
of the preceding polynomial substitution.

When `q j = C a * X` and `a` is nonzero, the inverse is the triangular change
with `j` entry `C a⁻¹ * X` and other coordinate polynomials
`-(q i).comp (C a⁻¹ * X)`. The two inverse identities are proved on every
commutative coefficient algebra by cancellation of `a` and `a⁻¹` and polynomial
evaluation under composition. Nilpotents are permitted in the value algebra.

For finite index sets, `polynomialShearRow` replaces the `j` entry of a row
`f` by `∑ i, (f i).comp (q i)`. If both rows consist of universally additive
polynomials, the transformed row is additive. The evaluation identity
`sum_eval₂_polynomialShearValues` says that applying `f` after the shear is
applying this transformed row. Its proof expands polynomial additivity and
separates the distinguished term in each finite sum.

`polynomialShearPoints` defines a group homomorphism on the points of every
relative scheme test, using the actual standard vector group's natural
coordinates and evaluating polynomials on global functions. The coefficient
homomorphism is the test scheme's structure map. Polynomial evaluation commutes
with pullback of global functions, so these point maps are natural under every
relative scheme morphism. `polynomialShearHom` is the resulting actual
group-scheme homomorphism, constructed by the existing pointwise Yoneda adapter.

`polynomialShearIso` pairs that homomorphism with the inverse triangular
homomorphism. Its two categorical inverse identities follow from the
all-algebra inverse identities through the natural coordinate equivalences.
`polynomialShearHom_comp_polynomialRow` and its isomorphism version establish
that the row-transformation identity is equality of actual group-scheme
morphisms, by testing all relative schemes and their vector coordinates.

This module constructs elementary coordinate changes and their row identities.
It does not yet iterate them to a zero coordinate, construct a vector-factor
decomposition, or prove the general unipotent woundness criterion. Those are
separate remaining steps. The statements impose no smoothness, connectedness,
or unipotence premise on a polynomial kernel.
