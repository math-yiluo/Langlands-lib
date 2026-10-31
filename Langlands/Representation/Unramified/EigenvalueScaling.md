# Scalar multiplication of the existing unordered spectra

This internal extension of `Unramified.Eigenvalues` defines `Eigenvalues.scale a s`
by mapping multiplication by the complex unit `a` over the existing symmetric
power. The rank and every repeated eigenvalue are retained. The tuple formula,
identity and product laws, compatibility with direct sums, and compatibility
with natural powers are proved by the corresponding symmetric-power maps.

`powerTrace_scale` gives multiplication by `a^k` on the `k`-th power trace.
`eulerPolynomial_scale` identifies the new Euler denominator with the old
polynomial after substitution of `a X` for `X`. Its proof represents the
spectrum by a tuple and compares the individual factors `1 - z_i X`.
The coefficient theorem follows from the polynomial coefficient formula
for this substitution.

`elementaryCoefficient_scale` proves multiplication by `a^i` on the existing
signed Euler coefficient. `standardHeckeScalar_scale` gives exactly the same
factor on the existing standard Hecke scalar for every index from zero through
the full positive rank, over a p-adic field in any universe. The positive
square-root residue-cardinality normalization is retained.

Provenance is internal algebra on the published unordered nonzero spectra,
their Euler polynomials, and their normalized Hecke scalar definition, using
Mathlib's symmetric powers, polynomial substitution and coefficient formula.
The file constructs no representation or Hecke eigenvector. It supplies no
spectrum existence or classification theorem, and it makes no assertion about
an actual character, representation twist or Weil/Galois matching.
