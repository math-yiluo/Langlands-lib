# Actual spherical Hecke operators for GL_n

This module specializes the actual compact-open Hecke corner and its integrated
fixed-vector action to `GL_n` over a finite extension of `Q_p`. It constructs
the standard diagonal double-coset operators, defines their prescribed scalars
from multiplicity-preserving spectra, and proves invariance of the resulting
spectral relation under representation equivalence. It does not assert that a
principal-series spectrum satisfies this relation.

## Scope and actual carriers

Fix `F : PadicField.{uF} p` with `[Fact p.Prime]`. The field topology, valuation,
uniformizer and finite residue cardinality are the canonical ones. The rank is
`n = r + 1`, hence positive. All matrix groups carry the canonical topology and
its Borel measurable structure. Coefficients are complex.

`sphericalOpenSubgroup F r` has exactly the existing subgroup
`Correspondence.sphericalSubgroup F r = GL_(r+1)(O_F)` as its underlying
subgroup. Its openness and `sphericalOpenSubgroup_isCompact` are proved by
identifying it with the existing level-zero congruence subgroup and applying
that subgroup's topology theorems. No replacement subgroup or conditional
compactness witness is supplied by a caller.

`sphericalHaar F r` is the existing `RankinSelberg.normalizedCompactOpenHaar`
construction applied to this compact open subgroup. `sphericalHaar_isHaar`,
`sphericalHaar_self` and `sphericalHaar_real_self` prove respectively the Haar
property and that the extended and real masses of the subgroup equal one.
The construction selects this Haar measure; no new measure uniqueness theorem
is proved here.

`AutomorphicObject.{uF,uV} F r.succPNat` means an actual irreducible admissible
smooth local representation, with carrier universe `uV` independent of the
field universe. This existing name imposes no global automorphy condition.
The module places no topology or finite-dimensionality assumption on its
ambient representation space. Equivalence results permit an independent
second carrier universe `uW`.

## Double cosets, corner and operators

`standardDiagonal F r i`, for `i : Fin (r + 2)`, is the actual invertible
diagonal matrix with the canonical uniformizer in the first `i.val` positions
and one elsewhere. It uses `GeneralLinear.Iwasawa.diagonalUnits` on actual
field units. `standardDiagonal_val` proves the entry formula; at index zero,
`standardDiagonal_zero` proves that it is the identity matrix.

`SphericalHeckeAlgebra F r` abbreviates the published convolution corner for
this Haar measure and compact open subgroup. `standardHeckeElement F r i`
applies `HeckeAlgebra.Corner.doubleCoset` to the standard diagonal matrix.
Since the subgroup has mass one, `standardHeckeElement_apply` proves that
this is precisely the characteristic function of the actual double coset
`K diag(ϖ,...,ϖ,1,...,1) K`. There is no division by the mass of that double
coset. `standardHeckeElement_zero` identifies the zeroth element with the
corner unit.

`standardHeckeOperator F A i` evaluates the existing `Hecke.cornerAction` at
this element. Its carrier is exactly
`fixedVectors A.obj.representation (sphericalSubgroup F r)`. Thus it is the
actual integrated action of the indicated characteristic function, using the
published convention `f(g) • A(g)v` and convolution `f(y)h(y⁻¹x)`.
`standardHeckeOperator_zero` follows from the unital corner action.

## Prescribed scalar and spectral relation

For `s : Eigenvalues n`, the existing `s.eulerPolynomial` is the product
`∏_j (1 - z_j X)` for any enumeration of the multiset `s`. Define

`elementaryCoefficient s i = (-1)^i * s.eulerPolynomial.coeff i`.

This is the signed-coefficient definition of the elementary symmetric
invariant; it retains repeated eigenvalues. The module proves its zeroth
value is one by evaluating the Euler polynomial at zero. It does not add a
separate subset-sum expansion theorem.

Writing `q` for the actual residue cardinality, `standardHeckeScalar F s i`
is, exactly in Lean,

`(Complex.ofReal (Real.sqrt (q : ℝ))) ^ (i.val * (n - i.val)) * elementaryCoefficient s i.val`.

The finite index ensures `0 ≤ i.val ≤ n`, so the natural subtraction has the
intended value. The square root is the nonnegative real square root, and `q`
is positive for the canonical finite residue field. This expression encodes
`q^(i(n-i)/2) e_i(s)` without a choice of a complex square root. There is no
extra half-rank shift of the eigenvalues. The zeroth scalar is proved to be
one, and `standardHeckeOperator_zero_scalar` proves the corresponding operator
identity for every object and spectrum.

`HasSphericalHeckeSpectrum F A s` is a proposition requiring both that the
actual spherical fixed submodule is nonzero and that, for every index and
every vector in it, the corresponding standard operator equals the prescribed
scalar times that vector. The nonzero clause prevents the relation from
holding vacuously on a representation with no spherical vectors. It imposes
no assumed fixed-space dimension or preselected spherical vector.

`standardHeckeOperator_equiv` specializes `Hecke.cornerAction_equiv` to these
elements. `hasSphericalHeckeSpectrum_iff_of_equiv` transports nonvanishing by
the existing fixed-vector equivalence, and transports each scalar equation
using its surjectivity, linearity and operator compatibility in both
directions. The second direction uses the inverse equivalence, so the two
ambient carrier universes remain independent.

`HasSphericalHeckeSpectrumClass` is the existential representative relation
on the genuine `AutomorphicClass` quotient. The proved
`hasSphericalHeckeSpectrumClass_classOf` identifies it with the object relation
on every representative, using the existing characterization of equality of
classes by genuine representation equivalence.
`HasSphericalHeckeSpectrumClass.isSpherical` extracts the nonzero fixed-space
witness.

## Provenance and remaining comparison

The construction is derived from the existing Library topology, Haar,
fixed-vector, corner-action and eigenvalue APIs. The intrinsic proofs above
are internal specializations of those APIs and elementary polynomial facts.
The choice of generators and scalar convention follows Benedict H. Gross,
*On the Satake isomorphism* (1998), registered as
`gross-1998-satake-isomorphism`, retained PDF SHA-256
`9bd0077b2057edd32885e46fd38872f423a4d45fef6bec0aa181af32dee062b3`:

- Section 2, PDF page 3, (2.1) and (2.5): `K = G(O_F)`, actual compactly
  supported bi-invariant functions, convolution and Haar mass one on `K`.
  Our complex corner uses these same functions and measure convention.
- Section 3, PDF page 6, (3.3)-(3.4): the positive half-modulus convention.
  PDF page 8, (3.14), gives the transform of the characteristic function
  of precisely our standard diagonal double coset as
  `q^(i(n-i)/2)` times the character of the `i`th exterior power.
- Section 6, PDF page 11, (6.3), describes the actual fixed-space action.
  PDF page 12, (6.5)-(6.7), identifies the signed Euler coefficients and
  their `q^(-i(n-i)/2)` relation to these Hecke eigenvalues. For a diagonal
  complex spectrum this motivates the signed-coefficient definition above.

These source formulas specify the intended normalization. The present module
only defines the scalar relation; it does not prove the Satake transform,
scalar action on spherical irreducibles, uniqueness or existence of a
spectrum, generation or commutativity of the Hecke algebra, or the equivalence
with `HasSphericalSpectrum` from normalized principal series. That last
comparison remains an independent statement and proof obligation. No local
reciprocity or Frobenius choice is used in these definitions.
