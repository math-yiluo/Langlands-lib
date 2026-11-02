# The lattice step in the diagonal-torus centralizer calculation

Worker 176.

This helper imports the published `Torus.Lattice`. It supplies the lattice
calculation used by `GeneralLinearGenericCentralizer` to specialize to the
actual `GeneralLinear.diagonalTorus` and rational genericity predicate.
The diagonal torus is published in `Reductive.RootDatum` and the rational
genericity predicate in `Rational.RelativeRoots`. This module does not prove
`GeneralLinearRationalStatement`.

For a split torus over an integral domain, `latticePairing_proj_sub` proves
that the pairing of the coordinate-character difference `proj i - proj j`
with a cocharacter is the difference of its `cocharacterLatticeEquiv`
coordinates. This follows directly from bilinearity and the lattice
definitions. `coordinatePairings_ne_zero_iff_injective` identifies avoiding
all those hyperplanes with injectivity of the integral weight function.

For any homomorphism from the actual split torus indexed by `ULift.{u} n` to
`GL_n` with the diagonal point formula on every test scheme,
`cocharacter_comp_eq_diagonalCocharacter_of_diagonal_points` identifies the
composite of a cocharacter with the Library's `diagonalCocharacter`.
Its weight at `j : n` is the lattice coordinate at `ULift.up j`. The lift
allows arbitrary `k : Type u` while retaining the published `GL_n` interface
with `n : Type`. The proof uses the sibling's cocharacter point formula and
point extensionality, so it applies on arbitrary test schemes.

`dynamicCentralizer_eq_torusCentralizer_of_coordinate_pairings` combines that
factorization, the distinct-weight criterion, and
`GeneralLinearCentralizer`'s matrix calculation. The dynamic block-Levi
equality remains an explicit hypothesis of this reusable lemma and is
available from the published `Dynamic.GeneralLinearOrbit`. The diagonal
point formula and the coordinate-root pairings are also explicit hypotheses;
`GeneralLinearGenericCentralizer` supplies them from the actual
diagonal-torus and relative-root interfaces.

## Provenance

These are internal, derived steps for the `GL_n` specialization of the
torus-centralizer identification in Borel–Tits, *Groupes réductifs* (1965),
Theorem 4.15(a), printed pp.90–91 (PDF pp.37–38), and Milne, *Algebraic Groups*
(2017), Theorem 25.6(b) and its proof, printed pp.545–546 (PDF pp.561–562).
The coordinate characters and cocharacters use Milne's §12.a, printed p.230
(PDF p.246), Theorem 12.9, printed p.233 (PDF p.249), and Example 12.15,
printed p.236 (PDF p.252), through the sibling lattice construction. The
pairing formula is an immediate calculation from those definitions.
The extension to integral domains and all test schemes is derived. No
relative-root calculation, representability statement, or general reductive
centralizer theorem is claimed here.
