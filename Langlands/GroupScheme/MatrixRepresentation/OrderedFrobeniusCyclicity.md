# Ordered Frobenius cyclicity

This derived unit connects the original ordered additive parameters of an affine
group scheme to its intrinsic Frobenius distribution action. Its provenance is
the existing ordered-coordinate constructions, the actual coordinate and
distribution identifications, and `FrobeniusCyclicDetection`. It introduces no
external structural or representation-theoretic assumption as a proved fact.

Let `G` be an affine group scheme over a field `k : Type u`, and let `x` be an
ordered family of `d` homomorphisms from the one-dimensional additive group to
`G`. The order is the existing `orderedPoint` convention. The factors need not
commute. The theorem `coordinateMap_bijective_of_orderedPoint` shows that
bijectivity of this ordered point map on every commutative `k`-algebra implies
bijectivity of its actual coordinate pullback. Its proof uses the universal point
of `G` and the universal tuple of polynomial variables to construct the two
inverse identities.

For a bijective coordinate pullback `hx`, `generator x hx i` is the inverse image
of the polynomial variable `X i`. These generators give the inverse coordinate
algebra equivalence, vanish at the identity, and evaluate to the original
parameters on every ordered point. The resulting `polynomialCoordinates`
equivalence is proved equal to the original `coordinateEquiv`.

Suppose a commutative group scheme `S` acts on `G` by group automorphisms, and
the action scales the `i`th additive factor by the value of an actual character
`w i`. This scaling equation is required on every commutative coefficient
algebra. Preservation of the ordered product proves the corresponding
equivariance of `orderedPoint`, without interchanging factors. Surjectivity of
the chart then proves that each inverse coordinate generator belongs to the
actual coordinate weight space of `w i`.

For `p` with `[ExpChar k p]` and any natural `r`, the intrinsic top distribution
formed from these generators equals `distributionBasis` at
`bound p d r`, whose entries are `p^r - 1`. The proof tests both functionals on
the surjective coordinate quotient map and uses the equality of the coordinate
equivalences. Consequently, on any supplied finite matrix representation `ρ`,
the action of this distribution is exactly the original ordered
`coefficientOperator ρ x (bound p d r)`.

The final three theorems additionally require that `S` is a split torus and
that a supplied cocharacter `ν` pairs strictly positively with every `w i`.
If the displayed coefficient operator is nonzero on an original vector `v`,
`FrobeniusCyclicDetection` therefore gives:

- injectivity of the full intrinsic distribution orbit map at `v`;
- dimension `(p^r)^d` of the intrinsic origin orbit span, which includes tests
  over all commutative coefficient algebras;
- equality of that span with the entire original representation when its
  separately supplied dimension upper bound is `(p^r)^d`.

The chart, torus action, factor scaling, positive pairings and nonzero original
coefficient remain explicit hypotheses. The last conclusion also retains the
whole-representation dimension bound. This unit constructs neither a root chart
for a reductive group nor a highest-weight vector satisfying that nonvanishing,
and supplies no upper bound for the entire induced space. It does not prove
`SteinbergBigCellStatement`.
