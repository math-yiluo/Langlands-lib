# Spherical classification obligations for normalized principal series

This module states five separate representation-theoretic obligations for the
actual constructions of `Representation/Unramified/PrincipalSeries`. All
statements are proposition-valued definitions in `Langlands.Unramified`; none
is proved here or assumed by the underlying definitions. The final
`SphericalPrincipalSeriesStatement` is their conjunction.

## Precise scope and conventions

The field is an arbitrary `F : PadicField.{uF} p`, with `[Fact p.Prime]`,
its canonical valuation, uniformizer, and topology. The group is the actual
`GL_(r+1)(F)` for every natural `r`, and the fixed subgroup is the published
`Correspondence.sphericalSubgroup F r = GL_(r+1)(O_F)`. Scalars are the usual
complex field. The characters constructed from `z : Fin (r+1) → ℂˣ` are
`x ↦ z_i ^ ord(x)`, with no unitarity restriction. Their values at the
canonical uniformizer are exactly `z_i`.

`principalSeriesOfTuple` is the existing induction from the upper Borel,
normalized by the positive half-modulus. `IsSphericalConstituent` requires
nonzero spherical fixed vectors and the actual subquotient relation: a
subrepresentation of this induced representation has a surjective intertwiner
onto the object. Every `AutomorphicObject` used here is already an actual
smooth irreducible admissible local representation; its name asserts no global
automorphy. No genericity, temperedness, or finite-dimensional carrier
hypothesis is added.

`Eigenvalues (r+1)` is the multiset of complex units of cardinality `r+1`,
including multiplicities. `HasSphericalSpectrum` existentially quantifies an
enumerating tuple and requires the preceding constituent relation. The
statements do not substitute an arbitrary polynomial for a representation.

## The five targets

1. `SphericalConstituentExistenceStatement`: every ordered tuple `z` has an
   actual spherical irreducible admissible constituent. The existential object
   has carrier universe `uF`, sufficient for the induced carrier, its
   subspaces and quotients. This does not assert that a witness can be
   constructed on every smaller carrier universe.
2. `SphericalConstituentUniquenessStatement`: if tuples `z` and `w` have the
   same multiset, any spherical constituents `A` and `B` of their respective
   principal series are equivariantly linearly isomorphic. Their carrier
   universes `uV` and `uW` are independent of each other and of `uF`. This
   includes different orderings, not just uniqueness within one ordered
   induction. It asserts uniqueness of the isomorphism class, not a unique
   intertwining map or a prescribed embedding.
3. `SphericalSpectrumExistenceStatement`: every actual irreducible admissible
   object with a nonzero spherical fixed space has some spectrum in the
   defined relation. Equivalently, it occurs in some normalized unramified
   principal series. The input carrier universe is independent of `uF`.
4. `SphericalSpectrumUniquenessStatement`: two spectra related to the same
   actual object are equal as multisets. Multiplicities are included in this
   equality. Together with the proved invariance of the relation under
   equivalence, this also controls the spectrum on genuine isomorphism
   classes. The statement makes no additional Hecke-eigenvalue assertion.
5. `SphericalFixedLineStatement`: if the actual fixed submodule is nonzero,
   its complex `Module.finrank` is one. There is no assumed finite-dimensional
   ambient representation or chosen spherical vector.

The aggregate retains the universe parameters `uF`, `uV`, and `uW` and the
stated existential universe for the first target. It is not a record parameter
supplied to a definition, and no choice of a Satake parameter function is made.

## Original-source correspondence

The retained originals were read at the locations below. The representation
claims in Borel's discussion are used independently of his conjectural general
local Langlands packet conditions.

- Armand Borel, *Automorphic L-functions*, Corvallis Part II (1979), section
  10.4, printed pages 44–45, PDF pages 53–54. On page 45 Borel states that a
  spherical irreducible admissible representation is a constituent of an
  unramified normalized principal series and that its inducing character is
  determined modulo the relative Weyl group. He also explains the
  at-most-one spherical irreducible constituent using the spherical fixed
  space of the principal series. For split `GL_n`, the relative Weyl group
  permutes the `n` diagonal characters, so its orbit is exactly their multiset.
  These assertions give the exhaustion and uniqueness targets, including
  independence of ordering.
- Borel, sections 7.1–7.2, printed pages 38–39, PDF pages 47–48: spherical
  Hecke characters correspond to semisimple classes, and the spherical
  fixed-vector space of an irreducible admissible representation is
  one-dimensional. This supplies the fixed-line target. Section 9.5,
  printed pages 42–43, PDF pages 51–52, identifies unramified torus characters
  via the valuation lattice, matching the explicit inducing characters.
- Benedict H. Gross, *On the Satake isomorphism* (1998), section 6, PDF page
  11, especially Proposition 6.4: the map from irreducible unramified
  representation classes to semisimple classes in the dual group is a
  bijection; the preceding paragraph states the bound of one on the
  spherical fixed-space dimension. For `GL_n`, every multiset of nonzero
  complex numbers gives an invertible diagonal semisimple class. Combining
  this existence with Borel's principal-series identification in 10.4 gives
  the first target for every ordered character tuple. Admissibility and the
  carrier realization are retained as formal proof obligations, not omitted
  from the existential conclusion.

The split `GL_n` specialization uses the standard identification of semisimple
conjugacy classes with multisets of nonzero eigenvalues; no Lean proof of that
matrix classification is claimed by this statement module. Likewise the
comparison between the Hecke parameter and the normalized inducing character
is part of the literature justification, not a theorem already proved here.
Borel's page 45 explicitly states consistency with the Hecke description of
section 7.2. Gross section 3, formula (3.14), PDF page 8, records the positive
half-modulus normalization for the `GL_n` double-coset generators. These
conventions use the inducing values `z_i` without an extra half-rank shift.

No local reciprocity or Frobenius convention is required: these statements
speak only about field characters and representations. A future comparison
with a Weil parameter must impose its own reciprocity convention.

Source identities:

- `borel-1979-automorphic-l-functions`, retained `Part II.pdf`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- `gross-1998-satake-isomorphism`, retained 17-page author text, SHA-256
  `9bd0077b2057edd32885e46fd38872f423a4d45fef6bec0aa181af32dee062b3`.

## Separate Hecke obligation

No statement here identifies the elementary symmetric functions of a related
spectrum with eigenvalues of actual double-coset Hecke operators. That
comparison still needs the actual normalized operators and an independent
statement. In the normalization of Gross (3.14), the operator for the double
coset of `diag(ϖ,...,ϖ,1,...,1)`, with `i` copies of `ϖ`, has spherical
eigenvalue `q^(i(n-i)/2)` times the `i`th elementary symmetric function. Gross
(6.5)–(6.7), PDF page 12, then gives the Euler denominator `∏(1-z_i X)`.
The present five targets neither implement nor assume that operator formula.
