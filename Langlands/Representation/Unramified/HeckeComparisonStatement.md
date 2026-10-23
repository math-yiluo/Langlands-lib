# Comparison of normalized principal-series spectra and actual Hecke operators

`Langlands.Unramified.SphericalHeckeComparisonStatement` is a proposition-valued
definition stating the missing comparison between the two actual spectral
relations. It is not proved in this module or assumed by their constructions.

For a fixed finite extension `F : PadicField.{uF} p`, `[Fact p.Prime]`, it
quantifies every positive rank `n = r + 1`, every actual smooth irreducible
admissible complex representation `A : AutomorphicObject.{uF,uV} F r.succPNat`,
and every multiset `s : Eigenvalues n` of `n` nonzero complex numbers. The
carrier universe `uV` is independent of `uF`. The existing object name does
not assert global automorphy. There is no genericity, unitarity, temperedness
or finite-dimensional ambient carrier hypothesis.

The assertion is exactly

`HasSphericalSpectrum F A s ↔ HasSphericalHeckeSpectrum F A s`.

The left side means that some tuple enumerating `s` defines continuous
unramified characters, with these values at the canonical uniformizer, whose
existing normalized upper-Borel principal series has `A` as a spherical
subquotient. Subquotient means an actual subrepresentation with a surjective
intertwiner to `A`. Spherical means a nonzero fixed submodule for the actual
`K = GL_n(O_F)`.

The right side uses that same nonzero fixed submodule. The Haar measure gives
`K` mass one. For each `0 ≤ i ≤ n`, the actual integrated operator for
`1_(K diag(ϖ,...,ϖ,1,...,1) K)`, with `i` uniformizers, must act on every fixed
vector as the scalar

`(sqrt(q) : ℂ)^(i*(n-i)) * (-1)^i * (s.eulerPolynomial.coeff i)`.

Here `sqrt(q)` is the nonnegative real square root of the actual residue
cardinality, embedded into `ℂ`, and `s.eulerPolynomial = ∏_j (1-z_j X)`.
The nonzero condition excludes a vacuous spectral relation. The zeroth
operator and scalar already agree by construction, but the positive-index
operator equations and the full equivalence are unproved. There is no extra
half-rank shift in the inducing values and no inverse uniformizer in the
specified diagonal elements.

## Original-source derivation

The statement is a derived split-`GL_n` comparison combining the following
original-source facts, all read in the retained copies:

- Armand Borel, *Automorphic L-functions* (Corvallis Part II, 1979), section
  7.1-7.2, printed pages 38-39 / PDF pages 47-48: the spherical Hecke algebra
  is identified with functions on the torus modulo its relative Weyl group;
  the nonzero hyperspecial fixed space of an irreducible admissible
  representation is one-dimensional and carries the corresponding character.
- Borel, section 10.4, printed pages 44-45 / PDF pages 53-54, especially the
  final paragraph before the remark on page 45: the parameter of the
  normalized unramified principal series agrees with the class obtained
  from the actual Hecke character in section 7.2. The preceding paragraph
  also states exhaustion and determination modulo the relative Weyl group.
  These representation facts are used independently of the conjectural
  general local Langlands packet requirements surrounding that discussion.
- Benedict H. Gross, *On the Satake isomorphism* (1998), section 2, PDF page 3,
  (2.1), (2.5): the compact subgroup and convolution measure are exactly
  `K = G(O_F)` and Haar mass one on `K`. Section 3, PDF page 6, (3.3)-(3.4),
  specifies the positive half-modulus. Formula (3.14), PDF page 8, sends
  the characteristic function of the indicated standard diagonal double
  coset to `q^(i(n-i)/2)` times the `i`th exterior-power character.
- Gross, section 6, PDF page 11, (6.2)-(6.3), evaluates that character on the
  semisimple parameter and identifies the Hecke action on spherical fixed
  vectors. Formulas (6.5)-(6.7), PDF page 12, express the same elementary
  symmetric invariants by the signed coefficients of `det(1-sX)`.

For split `GL_n`, the Weyl group permutes the diagonal values, so these data
are a multiset with multiplicities. The forward implication combines Borel's
identification with Gross's operator formula. The converse additionally uses
exhaustion by normalized unramified principal series and the fact that all
signed coefficients of the normalized product determine the multiset of
nonzero values. This algebraic separation argument and the representation
theorems remain part of the proof obligation; defining a relation does not
supply them. No local reciprocity, Frobenius convention, global induction
or chosen Satake parameter function is asserted.

Exact source identities:

- `borel-1979-automorphic-l-functions`, retained `Part II.pdf`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- `gross-1998-satake-isomorphism`, retained author PDF, SHA-256
  `9bd0077b2057edd32885e46fd38872f423a4d45fef6bec0aa181af32dee062b3`.

The previously stated five spherical classification targets remain separate.
This comparison is an additional compatibility obligation on the actual
operators; it supplies no proof or replacement of those targets.
