# Actual radical intermediate fields and their norm symmetry

This is a derived support construction for the local norm-separation proof. The
base field `K : Type u` has arbitrary universe. All extensions constructed here
are actual intermediate fields of `AlgebraicClosure K`.

`radicalField K n a` is the field generated over `K` by the root set of
`X ^ n - C a` in that algebraic closure. The splitting-field and finite-dimensional
instances hold for every natural number `n` and every `a : K`. They use Mathlib's
root-set adjoining construction and the fact that an algebraically closed field
splits every polynomial.

With `NeZero n`, an irreducible binomial, and a primitive `n`th root of unity in
`K`, `radicalField_isAbelianGalois` and `radicalField_finrank` prove that this
extension is abelian Galois and has degree `n`. The former uses Mathlib's cyclic
Galois-group theorem and the implication from cyclic to abelian Galois. There is
no primality or local-field assumption in these results.

For a base unit `a`, `radicalUnit a` chooses Mathlib's root in the splitting field
and turns it into a unit. Its nonvanishing follows by raising a hypothetical zero
to the positive exponent `n` and contradicting the nonzero image of `a`.
`radicalUnit_pow` states the resulting equality in the unit group with the image
of `a` under the actual algebra map.

For units `a`, `b`, and `ζ`, assume both binomials `X^n-a` and `X^n-b` are
irreducible and that the field value of `ζ` is primitive of order `n`.
`radicalField_norm_iff` proves that `b` belongs to the determinant-norm subgroup
from the radical field of `a` if and only if `a` belongs to that from the radical
field of `b`. The proof uses their supremum as a common finite Galois extension,
installs the actual inclusion maps and scalar towers, and applies
`norm_iff_of_irreducible_radicals` from `KummerNormSymmetry` with the chosen unit
roots. Thus both norm groups refer to the actual radical intermediate fields.

The construction is derived from the published `KummerNormSymmetry` support and
Mathlib's `FieldTheory.KummerExtension` and intermediate-field APIs. Its
mathematical provenance is the radical-field norm symmetry used in Serre,
*Local Fields* (1979), XIV §2, Proposition 7(v) and the following corollary,
printed pages 208–209. The implementation proves that symmetry through explicit
carry classes, rather than introducing a local symbol. This unit does not prove
nontriviality of the norm quotient or unconditional separation of local units;
those arithmetic and topological arguments remain separate obligations.
