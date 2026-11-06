# Compact open averaging on the a.e. cuspidal L² subspace of `[G]`

Author: Worker 112.

The published module `GroupSchemeRestrictionFullAEL2` defines the
almost-everywhere cuspidal subspace `quotientFullAEL2CuspidalSubmodule` of `L²`
of the restriction split-centre quotient `RestrictionSplitCentre.Quotient F G S j`.
This quotient has the shape `[G] = A_G G(F) \ G(A_F)` of Getz--Hahn
(2.20)--(2.21) (`getz-hahn-2024-automorphic-representations`, printed
pp. 68--69). The subspace follows their (6.20)--(6.21) (printed p. 168). The
published `GroupSchemeRestrictionFullAEL2Hilbert` makes the subspace a Hilbert
space with an orthogonal projection. The published
`GroupSchemeRestrictionFullAEL2Continuity` gives the bounded and jointly
continuous cuspidal right action. The published
`GroupSchemeRestrictionQuotientL2FiniteAverage` averages the right action on
all of `L²([G])` over a compact open subgroup of the finite adelic points.

The present module carries out that averaging on the cuspidal subspace. It is
the `[G]` counterpart of the published positive-torus module
`GroupSchemeFullAEL2FiniteAverage`. It proves that the published
`fullAEL2CuspidalEquiv` carries the positive-torus cuspidal average to the new
one.

## Data and hypotheses

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type. `hG : IsConnectedReductive G`, and
  `hPD : ParabolicDynamicStatement.{0}` is the structural hypothesis taken by
  the published cuspidal subspace.
- `S` is a commutative group scheme over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`.
- `T` is a commutative group scheme over `F` and `i : T.toGrp ⟶ G`, with
  `h : subgroup F G S j = imageSubgroup F T G i`.
- `characterRestrict i` is injective (`hi`) with finite-index range,
  `hc : IsCentral i`, and `hT : IsSplitTorus T.toGrp`.
- Haar measure on `normOneSubgroup F G` is right invariant (an instance
  argument), and `hInv'` is any proof of
  `QuotientRightInvariant F G μ`, where `μ = quotientHaarMeasure F G S j`.
  Every result holds for whichever proof is given.
- `K` is an actual open subgroup of `FiniteAdelicGroupPoints F G`, with the
  original finite adelic topology.

Write `Sq` for `quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT`,
`Rc(g)` for the published cuspidal right action
`quotientFullAEL2CuspidalRightAction`, and `ι = AdelicGroupPoints.ofFinite F G`
for the published continuous inclusion of the finite adelic points.

## Restriction to the finite adelic points

- `quotientFullAEL2CuspidalFiniteRightAction` is the representation of
  `FiniteAdelicGroupPoints F G` on `Sq` obtained by composing `Rc` with `ι`.
  Its `_apply` lemma holds by definition.
- `quotientFullAEL2CuspidalCompactOpenAction` is the homomorphism from `K` to
  `Sq →L[ℂ] Sq`. It composes the published
  `quotientFullAEL2CuspidalBoundedRightAction` with `ι` and the subgroup
  inclusion. Its `_apply` lemma holds by definition.
- `norm_quotientFullAEL2CuspidalCompactOpenAction` proves
  `‖Rc(ι k) φ‖ = ‖φ‖`, by the published norm equality for the bounded action.
- `continuous_quotientFullAEL2CuspidalCompactOpenOrbit` proves that
  `k ↦ Rc(ι k) φ` is continuous on `K` with the subgroup topology. It composes
  the published continuous orbit `quotientFullAEL2CuspidalOrbitMap φ` with `ι`
  and the subtype inclusion.

## Averaging over a compact open subgroup

Now assume `[CompactSpace K]`. By Mathlib's `isCompact_iff_compactSpace`, this
is equivalent to compactness of `K` as a subset of the finite adelic points. On
`K` the module reuses the published positive-torus local instances: the
topological group structure of the subgroup, second countability induced from
the finite adelic points, and the Borel σ-algebra. The group integral is taken
against the published normalized Haar probability measure
`compactProbabilityHaar K`. This measure on `K` is different from the
quotient measure `μ` that defines the `L²` norm. The integral is formed in
`Sq`, which is complete by the published `GroupSchemeRestrictionFullAEL2Hilbert`.

- `quotientFullAEL2CuspidalFiniteAverage` is the bounded operator
  `compactIsometricAverage K πK _ _`, where `πK` is the compact open action
  above. Write `P` for it.
- `quotientFullAEL2CuspidalFiniteAverage_apply` gives its value
  `∫ k : K, Rc(ι k) φ ∂(compactProbabilityHaar K)`.
- `quotientFullAEL2CuspidalFiniteAverage_integrable` proves Bochner
  integrability of the orbit for every cuspidal vector.
- `norm_quotientFullAEL2CuspidalFiniteAverage_le` bounds the operator norm by
  `1`.
- `quotientFullAEL2CuspidalFiniteAverage_fixed` proves `Rc(ι k) (P φ) = P φ`
  for every `k : K`.
- `quotientFullAEL2CuspidalFiniteAverage_eq_self_iff` proves that `P φ = φ`
  exactly when `φ` is fixed by every element of `K`.
- `quotientFullAEL2CuspidalFiniteAverage_idempotent` proves `P ∘ P = P`.

These results are the corresponding published facts about
`compactIsometricAverage`, applied to `πK`.

- `quotientFullAEL2CuspidalFiniteAverage_mem_fixedVectors` proves that every
  output lies in the published `Langlands.fixedVectors` submodule of
  `quotientFullAEL2CuspidalFiniteRightAction` for `K`.
- `quotientFullAEL2CuspidalFiniteAverage_isSmoothVector` proves that every
  output is a `Langlands.IsSmoothVector` of the finite cuspidal action, with
  witness `K`.
- `quotientFullAEL2CuspidalFiniteFixedRetraction` is the average with codomain
  the `K`-fixed cuspidal vectors. `_val` says that its underlying vector is
  `P φ`, and `_inclusion` says that it is the identity on `K`-fixed vectors.

## Compatibility with the average on `L²([G])`

Write `A` for the published `rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K`
on `L²([G])`.

- `quotientFullAEL2CuspidalFiniteAverage_val` proves `(P ψ).val = A ψ.val` for
  every cuspidal vector `ψ`. The proof applies the published
  `compactIsometricAverage_intertwiner` to the published isometric inclusion
  `quotientFullAEL2CuspidalInclusionLI`, which intertwines the two compact open
  actions by definition.
- `rationalQuotientL2FiniteAverage_mem_quotientFullAEL2CuspidalSubmodule`
  concludes that `A` maps `Sq` into `Sq`.
- `quotientFullAEL2CuspidalOrthogonalProjection_finiteAverage` proves that the
  published orthogonal projection onto `Sq` carries `A φ` to `P` applied to the
  projection of `φ`, for every `φ` in `L²([G])`. It applies the same
  intertwiner lemma to the projection, using the published equivariance
  `quotientFullAEL2CuspidalOrthogonalProjection_rightAction`.
- `quotientFullAEL2CuspidalAmbientProjection_finiteAverage` gives the
  corresponding identity for the ambient projection: it commutes with `A`.

## Comparison with the positive-torus quotient

`fullAEL2CuspidalEquiv_finiteAverage` takes explicit splitting coordinates `I`
and `e : T.toGrp ≅ splitTorus (Spec F) I` in place of `hT`. It proves that the
published isometric equivalence `fullAEL2CuspidalEquiv F G hPD hG h hi I e hc`
carries the published positive-torus `fullAEL2CuspidalFiniteAverage` to
`quotientFullAEL2CuspidalFiniteAverage`, where the split-torus proof is the one
built from `I` and `e`. On underlying `L²` classes this is the published
`quotientL2Equiv_finiteAverage`, applied after the published
`fullAEL2CuspidalFiniteAverage_val` and before
`quotientFullAEL2CuspidalFiniteAverage_val`.

## Split components

Assume `hj : IsSplitComponent j` and `hs : IsSplitComponent i`, injectivity and
finite index of `characterRestrict i`, the norm-one right-invariance instance
and `[CompactSpace K]`. The comparison equality is the published
`subgroup_eq_of_splitComponents`, right invariance of `μ` is the published
`quotientHaarMeasure_rightInvariant_of_splitComponents`, and centrality and the
split-torus property come from `hs`.

- `splitComponentFullAEL2CuspidalFiniteAverage` is the average on the published
  `splitComponentFullAEL2CuspidalSubmodule`. Its `_val` lemma recovers the
  published `splitComponentL2FiniteAverage`.
- `norm_splitComponentFullAEL2CuspidalFiniteAverage_le` bounds its operator
  norm by `1`, and `splitComponentFullAEL2CuspidalFiniteAverage_isSmoothVector`
  proves that every output is a smooth vector of the finite cuspidal action.
- `splitComponentFullAEL2CuspidalOrthogonalProjection_finiteAverage` states
  that the published split-component orthogonal projection intertwines
  `splitComponentL2FiniteAverage` with the cuspidal average.

## Provenance and scope

The quotient follows Getz--Hahn (2.20)--(2.21) and the cuspidal subspace their
(6.20)--(6.21). Every construction here is internal. It applies the published
`compactIsometricAverage` to the published bounded and jointly continuous
cuspidal right action, and compares the result with the published average on
`L²([G])` and with the published positive-torus cuspidal average. No literature
theorem is attributed to this module.

The module proves smoothness for the finite adelic action of its outputs only.
It does not prove density of smooth vectors, convergence of the averages as `K`
shrinks, archimedean smoothness, admissibility, or any spectral decomposition.
It does not prove existence of split components, injectivity or finite index
of `characterRestrict i`, `ParabolicDynamicStatement`, or finite volume.
Norm-one right invariance is an instance hypothesis. For connected reductive
`G` the published `normOneHaar_isMulRightInvariant_of_connectedReductive`
supplies it; this module does not invoke that result.
