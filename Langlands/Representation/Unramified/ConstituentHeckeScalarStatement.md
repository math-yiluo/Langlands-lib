# Standard Hecke scalars of spherical principal-series constituents

`Langlands.Unramified.SphericalConstituentHeckeScalarStatement` is a
proposition-valued definition. It states an unproved obligation; it is not
proved or assumed in this module.

## Statement

For every prime `p` with `[Fact p.Prime]`, every finite extension
`F : PadicField.{uF} p`, every `r : ℕ` (so the rank is `n = r + 1`), every
ordered tuple `z : Fin (r + 1) → ℂˣ` and every actual smooth irreducible
admissible complex representation `A : AutomorphicObject.{uF,uV} F r.succPNat`,
with independent carrier universe `uV`,

`IsSphericalConstituent F z A → HasSphericalHeckeSpectrum F A (Eigenvalues.ofTuple z)`.

The hypothesis `IsSphericalConstituent F z A` means that the fixed submodule of
`A` for `K = GL_n(O_F)` (`sphericalSubgroup F r`) is nonzero and that `A` is a
subquotient (an actual subrepresentation with a surjective intertwiner onto `A`)
of the existing normalized upper-Borel principal series `principalSeriesOfTuple F z`,
induced from the continuous unramified characters taking the values `z j` at the
canonical uniformizer. No genericity or regularity of `z` is assumed.

The conclusion `HasSphericalHeckeSpectrum F A (Eigenvalues.ofTuple z)` means that
the same fixed submodule is nonzero and that, for every `0 ≤ i ≤ n`, the actual
integrated operator `standardHeckeOperator F A i` of the characteristic function
of `K diag(ϖ,...,ϖ,1,...,1) K` (`i` uniformizers; Haar measure with `K` of mass
one) acts on every fixed vector as the scalar `standardHeckeScalar F (ofTuple z) i`,
namely

`(sqrt(q) : ℂ)^(i*(n-i)) * (-1)^i * coeff_i (∏_j (1 - z_j X))`,

that is, `q^(i(n-i)/2)` times the `i`th elementary symmetric function of the
values `z j`, where `q` is the actual residue cardinality and `sqrt(q)` its
nonnegative real square root.

Since `HasSphericalSpectrum F A s` is by definition
`∃ z, Eigenvalues.ofTuple z = s ∧ IsSphericalConstituent F z A`, this statement is
equivalent to the forward implication of
`Langlands.Unramified.SphericalHeckeComparisonStatement`; it is stated separately
because the spherical constituent uniqueness proof needs only this direction,
for every carrier universe at once.

## Original-source derivation

The statement is derived (provenance: derived) for split `GL_n` from:

- Armand Borel, *Automorphic L-functions* (Corvallis Part II, 1979), sections
  7.1-7.2, printed pages 38-39 / PDF pages 47-48: the spherical Hecke algebra is
  identified with Weyl-invariant functions on the unramified characters of the
  torus by the Satake transform, and a class-one representation defines a
  character of it; section 10.4, printed pages 44-45 / PDF pages 53-54: an
  irreducible constituent with a nonzero hyperspecial fixed vector of the
  normalized unramified principal series of the character with Satake class `t`
  has Hecke character given by `t`.
- Benedict H. Gross, *On the Satake isomorphism* (1998): section 3, PDF page 6,
  (3.3)-(3.4), the Satake transform with the positive half-modulus; (3.14), PDF
  page 8, the transform of the characteristic function of the `i`th standard
  double coset is `q^(i(n-i)/2)` times the trace of the `i`th exterior power;
  section 6, PDF pages 11-12, (6.2)-(6.3) and (6.7), the corresponding
  eigenvalue on the spherical vector is the value of that character at the
  semisimple parameter, and these are the signed coefficients of `det(1 - sX)`.

Combining these, the scalar of the `i`th standard operator on a spherical
constituent of the principal series attached to `z` is `q^(i(n-i)/2) e_i(z)`,
which is the scalar `standardHeckeScalar F (ofTuple z) i` of the Library.

Exact source identities:

- `borel-1979-automorphic-l-functions`, retained `Part II.pdf`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- `gross-1998-satake-isomorphism`, retained author PDF, SHA-256
  `9bd0077b2057edd32885e46fd38872f423a4d45fef6bec0aa181af32dee062b3`.
