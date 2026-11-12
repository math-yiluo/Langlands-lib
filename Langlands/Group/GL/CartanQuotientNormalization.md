# Constructing normalized Cartan coordinates

Author: Worker 952.

`Langlands.GeneralLinear.CartanQuotient.normalize` constructs an element of the
existing `NormalizedTuple (m + 1)` from an antitone tuple
`lam : Fin (m + 1) → ℤ`. Its coordinate at `i` is
`lam i - lam (Fin.last m)`. The positive rank is expressed as `m + 1`;
there is no arbitrary choice of an index and no rank-zero normalization.
The constructor imports the published intrinsic laws and changes none of
their definitions, statements, or proofs.

## Construction and laws

Antitonicity is preserved by common translation (`antitone_shift`).
The last coordinate of the translated tuple is zero, so the published
`normalized_iff_antitone_last_eq_zero` proves that its coordinates are
nonnegative and that one attains zero. This proof is the certificate in
the subtype, not a Cartan decomposition supplied as data.

`normalize_apply` gives the coordinate formula, and `normalize_last`
evaluates the last coordinate. `normalize_eq_self` shows that normalization
fixes an already normalized tuple. `normalize_shift` shows that a common
integer shift has no effect on the normalized tuple.
`normalize_eq_iff_shift` proves the converse as well: two antitone tuples
have the same normalization precisely when one is a common integer shift
of the other. In the forward direction, equality of coordinates after
subtracting the last entries gives the shift
`mu (Fin.last m) - lam (Fin.last m)`; the reverse direction uses
`normalize_shift`. This classifies integer tuples under translation. It
does not prove that equality of quotient cells forces a common shift.

For any prime `p`, `F : PadicField.{uF} p` and supplied
`T : F.TopologicalData`, `subgroupCell_normalize` and `cell_normalize`
preserve the actual sets in the central quotient.
The first holds for every subgroup `H`, including every
`H ≤ maximalCompact T (m + 1)`. The unchanged quotient images allow the
same two factors from `H`; no scalar-membership premise is required.
`quotientMap_representative_normalize` is the corresponding equality of
the two diagonal representatives' quotient images.
`degree_normalize` and `delta_normalize` preserve the existing finite
positive-root sum and the full upper-Borel modulus weight.
These construction comparisons are specializations of the published
common-shift laws, using the shift `-lam (Fin.last m)`.
There is no claim that `height` is invariant under translation.

The field universe `uF` is arbitrary. No representation carrier or
representation hypothesis occurs, and no topology is installed.

## Existing concrete API and exact remaining boundary

The original construction remains in `Langlands.Group.GL.CartanQuotientDefinitions`.
Its namespace is `Langlands.GeneralLinear.CartanQuotient`:

| Object | Existing declaration |
| --- | --- |
| Integral subgroup `GL_n(O_F)` inside the actual group | `maximalCompact T n` |
| Uniformizer-power diagonal | `representative T lam` |
| Quotient by the entire matrix-group center | `centralQuotient F n`, `quotientMap F n` |
| Quotient images of `H a(lam) H` and `K a(lam) K` | `subgroupCell T H lam`, `cell T lam` |
| Decreasing tuples with nonnegative coordinates and an attained zero | `Normalized`, `NormalizedTuple` |
| Root sum, modulus and coordinate height | `degree`, `delta T`, `height` |
| Actual singleton-Levi and upper-Borel diagonals | `representativeLevi T lam`, `representativeBorel T lam` |

`Langlands.Group.GL.CartanQuotientLawsProof` proves the closed proposition
`cartanQuotientLaws : CartanQuotientLawsStatement`. Its named helpers
include membership and subgroup containment, scalar killing and shift
compatibility, degree shift invariance and nonnegativity, positivity of
delta and height, the diagonal normalized-absolute-value formula and
its monotonicity, and equality of delta with the actual upper-Borel
modulus. These are published results imported by this constructor,
not new hypotheses.

The chosen uniformizer has normalized absolute value `q⁻¹`, so the diagonal
entries have absolute values `q^(-lam i)`. Thus **antitone** exponents give
**monotone** absolute values. Subtracting the last exponent fixes the
minimum at zero and changes the diagonal by a central uniformizer power,
leaving its quotient image unchanged. The full upper modulus is
`q^(-degree lam)`, rather than its inverse or square root.

`Langlands.Group.GL.CartanQuotientCoverStatement` separately states
`CartanQuotientCoverStatement` and `CartanQuotientDisjointStatement`.
This constructor does not prove them. Their remaining proof requires
the supplied-`T` uniformizer adapter, lifting quotient equality through
the full scalar center, splitting an arbitrary scalar unit into a
uniformizer power and a valuation-one unit, integral membership of the
latter scalar matrix, and application of the unique exponents in
`GeneralLinear.Cartan.cartanDecomposition`. This is a substantive
algebraic quotient argument beyond the normalization construction.
The focused proof successor is Task 1443,
`6680f0d4-3690-408c-a3fd-517e4537f703`. Its shared draft is unreviewed and
is not imported here.

No covering, uniqueness, compactness, measurability, Haar-volume bound,
analytic convergence, coefficient estimate or temperedness claim is
stored in the constructed objects. The coordinate height is the internal
weight `1 + ∑ |lam i|`; it is not identified with Waldspurger's `1 + sigma`.

## Provenance

The constructor and its elementary integer identities are derived internal
constructions on the published concrete API, rather than verbatim results
from the literature. No unpublished draft implementation is used.

The mathematical conventions come from J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, I.1,
printed pp.239–242 (one-based PDF pp.5–8). Source ID
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Retained original:
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
These four pages were read for this pair. No source-specific errata note
was found in the available project or Library notes.

Printed p.239 defines the chamber by nonnegative simple-root coordinates.
Printed p.240 chooses the sign `q^(-⟨chi,H_G(g)⟩) = |chi(g)|`.
Equation (4), p.241, is the disjoint Cartan decomposition before the
additional central normalization. Equation (5), pp.241–242, uses the
inverse modulus in its volume bounds; those bounds are outside this
construction. Printed p.242 defines `sigma` through a matrix norm, so no
identification with the coordinate height is inferred.
