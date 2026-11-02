# Actual GL rational-point topology, subgroups and quotient

This module proves that the existing algebraic comparison from the rational
points of the actual GL group scheme to the existing matrix group is a
continuous multiplicative equivalence. It restricts that same comparison to
the dynamic block parabolic, Levi and unipotent subgroups, identifies their
continuous limit and inclusion maps with the existing matrix maps, and
compares the actual parabolic quotients.

All public declarations are in `Langlands.GroupScheme.GeneralLinear`.
The coefficient ring `R : Type u` is any commutative topological ring with
`IsTopologicalRing R`. The rank `N : ℕ` and block shape
`B : Langlands.GeneralLinear.BlockShape N` are arbitrary. There is no
positive-rank, field, Hausdorff or local-compactness hypothesis. In particular,
rank zero and its empty block shape are included.

## Provenance and reused constructions

This is an internal interface comparison, derived from the following existing
constructions rather than a new translation of a literature theorem.

- `Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv`,
  `rationalPointTopology` and `rationalPointHomeomorph` identify the identity
  test object with the base-valued affine point convention.
- `Langlands.AlgebraicGeometry.PointTopology.GeneralLinear.schemePointHomeomorph`
  compares those affine scheme points with matrix units, and
  `schemePointHomeomorph_apply` identifies its map with `affinePointsEquiv`.
- `Langlands.GroupScheme.GeneralLinear.rationalPointsEquiv` is the algebraic
  GL comparison at the identity test object. Its restrictions are
  `rationalParabolicEquiv`, `rationalLeviEquiv` and `rationalUnipotentEquiv`;
  `rationalLeviEquiv_limitHom` and `rationalParabolicEquiv_inclusion` identify
  the limit and its section with the existing matrix maps.
- `Corepresented.map_affineSectionsIso_pointsEquiv` and
  `Corepresented.affineSectionsIso_hom_ringHom` compare the global-sections
  and affine-algebra point conventions through `Scheme.ΓSpecIso`.
- `Dynamic.limitHom_inclusion`, `Dynamic.ker_limitHom` and
  `Dynamic.unipotent_subgroupOf_parabolic_normal` supply the actual algebraic
  section, kernel and normality. The existing matrix topology maps are
  `B.leviEquivContinuous`, `B.leviProjectionContinuous` and
  `B.parabolicQuotientLeviContinuous`.

The imported algebraic GL and affine-point modules retain their own original
source provenance. This module proves compatibility between their concrete
maps; it does not assume an additional representation-theoretic assertion.

## Exact topology

Write `G` for `groupScheme (Fin N) (CommRingCat.of R)`. Its rational-point
carrier is the actual morphism type
`Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X`.
The module explicitly installs, locally, the named
`rationalPointTopology R G.X`. This is the topology induced from the existing
affine evaluation topology by the identity-test equivalence. The affine
hypothesis follows from the existing GL group scheme.

The matrix group is the existing `Langlands.GeneralLinear N R`, the units
of the matrix ring with Mathlib's units topology. That topology records the
entries of a matrix and its inverse. Each dynamic subgroup carrier below has
the subtype topology from this particular rational-point topology. Each
matrix subgroup has the existing subtype topology. The quotients have the
quotient topologies. These statements do not assert a comparison for an
arbitrary topology on rational points, and install no global topology instance
on the rational-point carrier. Consumers use the same named topology explicitly.

## Ambient continuous multiplicative equivalence

`rationalPointsHomeomorph N R` composes `rationalPointHomeomorph` with
`GeneralLinear.schemePointHomeomorph (Fin N) R R`.
`rationalPointsHomeomorph_apply` proves that its value at every point is exactly
`rationalPointsEquiv N (CommRingCat.of R)`, not just an unspecified bijection.

The implemented proof first compares the matrices of the identity-test point
and its base-valued affine transport. Their entries are the pullbacks of the
same GL coordinate sections, because the transport preserves the underlying
scheme morphism. It then applies the existing corepresented affine-sections
comparison. On GL matrices the induced map is precisely entrywise application
of `Scheme.ΓSpecIso.hom`; this is the ring transport used in
`rationalPointsEquiv`. The scheme-point homeomorphism's underlying-map formula
finishes the equality.

`rationalPointsContinuousMulEquiv N R` packages the *existing*
`rationalPointsEquiv` with the two continuity proofs from that homeomorphism.
`rationalPointsContinuousMulEquiv_apply` records the unchanged underlying
map. `rationalPoints_isTopologicalGroup` transports the existing topological
group property of matrix units through the inducing multiplicative map.
It is a theorem for the explicitly selected topology, not a global instance
choosing a topology for every rational-point carrier.

## Dynamic subgroup comparisons and maps

Set `λ = blockShapeCocharacter B (CommRingCat.of R)` and let the test object
be the identity map of `Spec R`. The following are continuous multiplicative
equivalences restricting exactly the same ambient algebraic map:

| Declaration | Source | Target |
| --- | --- | --- |
| `rationalParabolicContinuousMulEquiv R B` | `(Dynamic.parabolic λ).carrier` at the test object | `B.parabolic R` |
| `rationalLeviContinuousMulEquiv R B` | `(Dynamic.centralizer λ).carrier` at the test object | `B.leviSubgroup R` |
| `rationalUnipotentContinuousMulEquiv R B` | `(Dynamic.unipotent λ).carrier` at the test object | `B.unipotentSubgroup R` |
| `rationalLeviProductContinuousMulEquiv R B` | the same dynamic centralizer points | `B.Levi R`, the existing product of block GL groups |

For each of the first three, forward and inverse continuity are restrictions
of the ambient continuous equivalence using subtype continuity. The fourth
composes the Levi restriction with the inverse of `B.leviEquivContinuous R`.

`rationalLimitContinuousHom R B` is the actual `Dynamic.limitHom λ` with
continuity proved by its existing algebraic comparison:
apply `rationalParabolicContinuousMulEquiv`, then the continuous block
projection, the continuous embedded-Levi equivalence and the inverse rational
Levi equivalence. Equality with the dynamic limit follows from
`rationalLeviEquiv_limitHom`. Thus
`rationalLeviProductContinuousMulEquiv_limit` states exactly

```text
rationalLeviProductContinuousMulEquiv R B (rationalLimitContinuousHom R B g)
  = B.leviProjection R (rationalParabolicContinuousMulEquiv R B g).
```

`rationalLeviInclusionContinuousHom R B` is the actual subgroup inclusion of
the centralizer points into the parabolic points; subtype continuity proves
it continuous. `rationalParabolicContinuousMulEquiv_inclusion` identifies it
with `B.leviAsParabolic R` under the two continuous comparisons.
`rationalUnipotentContinuousMulEquiv_conj` identifies the actual
`Dynamic.centralizerConj λ` action with matrix conjugation by the corresponding
embedded Levi matrix. Its proof uses the underlying conjugation formula and
the multiplicativity and inverse compatibility of `rationalPointsEquiv`.

## Actual quotients

`rationalUnipotentInParabolic R B` is literally
`((Dynamic.unipotent λ).carrier test).subgroupOf
  ((Dynamic.parabolic λ).carrier test)`.
It is not a replacement abstract kernel. The instance
`rationalUnipotentInParabolic_normal` reuses the existing dynamic normality
theorem. `rationalLimitContinuousHom_ker` identifies this subgroup with the
kernel of the actual limit homomorphism.

`rationalParabolicQuotientLeviContinuousMulEquiv R B` is a continuous
multiplicative equivalence from the quotient by this actual subgroup to
the dynamic centralizer points. Its algebraic equivalence transports the
denominator along `Dynamic.ker_limitHom`, then uses
`QuotientGroup.quotientKerEquivOfRightInverse` with the actual centralizer
inclusion as section. Forward continuity follows from the quotient-map
criterion and continuity of the limit. Inverse continuity follows from
continuity of the inclusion followed by the quotient map. The `_mk` and
`_symm_apply` lemmas specify the maps exactly:

```text
[g] ↦ rationalLimitContinuousHom R B g,
z   ↦ [rationalLeviInclusionContinuousHom R B z].
```

`rationalParabolicQuotientProductLeviContinuousMulEquiv R B` composes with
the continuous product-Levi comparison. Its `_mk` lemma sends `[g]` to
`B.leviProjection R (rationalParabolicContinuousMulEquiv R B g)`.
`rationalParabolicQuotientMatrixContinuousMulEquiv R B` then composes with
the inverse of the existing matrix quotient/product-Levi equivalence.
Its `_mk` lemma sends `[g]` to the class of
`rationalParabolicContinuousMulEquiv R B g` in
`B.parabolic R ⧸ B.unipotentRadical R`. The proof applies the injective matrix
quotient/product-Levi map and uses the two projection formulas.

## Scope and prerequisite status

These are actual continuous group and quotient comparisons, with the named
evaluation topology and the existing matrix models. They do not prove the
full Haar-to-block modulus identity, alter positive induction or inverse
Jacquet normalization, transfer finite length to further local-field models,
or establish the full graded Zelevinsky theorem. Those obligations retain
their existing owners and exact targets.

At preparation, the imported pairs `Dynamic/GeneralLinearRationalPoints`,
`PointTopology/GeneralLinear` and `PointTopology/RationalPoints` have separate
independent approvals but await publication. Their exact frozen copies are
used unchanged for validation; they are excluded from this contribution's
integrated paths. They must publish first. The present module needs its own
independent semantic review. Only its Lean/Markdown pair is submitted here.
