# The actual signed cut complex

Author: Worker 164.

This module constructs the finite signed complex whose terms are actual
normalized parabolic induction after normalized Jacquet restriction. Its degree
objects are smooth representations, its differentials are actual equivariant
linear maps, and consecutive differentials compose to zero. It supplies no
exactness, homology concentration or effectivity result.

For rank `n`, a set `s` of interior cuts in `Fin (n-1)` determines the consecutive
block shape `shape s = (BlockShape.cutEquiv n).symm s`. The carrier `Term T ρ s`
is exactly the smooth function space of

```text
T.normalizedParabolicInduced (shape s) (T.normalizedJacquet (shape s) ρ).
```

The positive induction half-modulus, inverse Jacquet half-modulus and right
translation are those of the existing functors. `transition T ρ h` is the
previously constructed actual `Transition.cutMap` for the inclusion `h : s ⊆ t`.
The cut-equivalence identifies its cut hypothesis with `h`.

`diagram T ρ` has these actual carriers and the linear parts of those actual
transition intertwiners. It proves the diagram identity and composition fields
using `cutMap_refl` and `cutMap_comp`. There is no extra coherence hypothesis in
the actual construction. Applying `SignedCutComplex` gives the degree `k` carrier

```text
∀ s : {s : Finset (Fin (n-1)) // s.card = k}, Term T ρ s.val.
```

This is a finite product of actual induction--Jacquet terms, and hence a model
for their finite direct sum. For positive rank, its indexing corresponds to
block shapes of length `k+1`, by the published formula `B.cuts.card=B.length-1`
and positivity of the length of a positive-rank shape. Rank zero is included in
the construction: there are no interior cuts, the degree-zero index is the empty
shape, and every positive degree has an empty index. The module does not identify
the rank-zero terminal class with the final signed-effectivity target.

`FiniteProduct.representation` gives a product its pointwise group action.
For finite index sets, `FiniteProduct.isSmooth` chooses an open stabilizer for
each coordinate of a vector and intersects the finitely many chosen subgroups.
The intersection fixes the whole vector. This proves smoothness without a
topology on coefficient modules and without finite-dimensionality or
admissibility. Each individual actual term is smooth by the existing
`smoothInduced_smooth` theorem.

The internal `EquivariantDiagram` lemmas show that equivariant diagram maps give
equivariant elementary insertion operators and an equivariant total
differential. Scalar linearity makes the insertion sign commute with the group
action. Extension of a homogeneous family by zero also commutes with the action.
Injectivity of this extension and its compatibility with the signed differential
then prove equivariance of each homogeneous differential. The actual application
discharges the map equivariance condition using `transition.isIntertwining'`.
Thus the generic lemmas add no hypothesis to the actual complex.

`differential T ρ k` is the resulting intertwiner from degree `k` to degree `k+1`.
Its linear part is exactly `(diagram T ρ).degreeDifferential k`, whose target
component at `s` is the sum over cuts `i ∈ s` of the actual map from `s.erase i`
to `s`, with scalar `(-1 : ℂ)^#{j ∈ s | j < i}`. Zero extension supplies the
source family. These are precisely the increasing exterior insertion
coefficients already proved in `SignedCutComplex`. Its square-zero theorem
therefore proves `ActualCutComplex.differential_square` on the actual
representations. The degree module is subsingleton when `n-1 < k`, because a
subset of `Fin (n-1)` cannot have that cardinality.

`degreeObject` bundles the actual smooth degree representation and
`degreeMorphism` bundles the differential in `SmoothRep`. The explicit cut
indexing and shape reconstruction are retained for the later terminal quotient
map. A canonical quotient from the full terminal degree, and any claimed
surjection from one specific induction summand, require their own constructions.

The parameters retain arbitrary primes, the supplied p-adic field and topology,
and independent field and coefficient universes. `Term` and each degree object
have carrier universe `max uF uV`; when the input is already saturated this
remains the same saturated universe. No input smoothness is needed to construct
the complex, since each induced term is restricted to its smooth vectors.
No irreducibility, quasicuspidality, finite length, admissibility or
classification hypothesis is used in this module.

The provenance is a derived implementation of the actual diagram used in
Ban--Jantzen, *The Langlands quotient theorem for finite central extensions of
p-adic groups II: intertwining operators and duality* (2016), section 4,
printed p.159, together with the internal finite signed-diagram construction.
The registered source is `ban-jantzen-2016-duality`, PDF SHA-256
`7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.
The pointwise quotient maps and their normalization have already been checked
in `TransitionMaps`. The later support-invariance, actual graded-map/exterior
comparison, exactness and terminal-homology class comparison remain separate
obligations. This module makes none of those claims.
