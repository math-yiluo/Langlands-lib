# Actual rational geometric stabilizer and radical projections

This internal construction specializes published closed stable dynamic limits
to the actual standard rational-point families. It provides algebraic
prerequisites for the proper-intersection geometric comparison in task
`f722f1c6-147e-453e-8664-02b7822b7bce`.

## Scope and literal subgroups

The field `k : Type u` is arbitrary. The group scheme `G` is affine and
connected reductive, `i` is an actual maximal split torus, and `ν` is a generic
cocharacter. The inputs include the published `StandardCocharacterStatement`
and `HasPointNormalizerComparison i`. The labels `I` and `J` are finite sets
of the literal `SimpleRoot i ν`; `n` is any point of the normalizer of
`torusPoints i`. No minimal-representative condition is used.

Write `P_I`, `M_I`, `U_I` for the exact `parabolic i ν I`, `levi i ν I`,
`unipotent i ν I` subgroups of `RationalPoint k G.X`. A supplied decomposition
`d_I : IsSemidirectDecomposition P_I M_I U_I` has the original projection
`r_I = d_I.projection`. The results hold for every such decomposition. Its
existence can separately be obtained from
`isSemidirectDecomposition_of_standardCocharacterStatement`, without adding
an independent decomposition premise to the rational expansion target.

The two maps and their literal images are as follows. The intersections in
this table are first formed in the ambient rational-point group, and then
restricted by `subgroupOf` to the displayed ambient parabolic or Levi.

| Declaration | Domain | Codomain | Formula |
| --- | --- | --- | --- |
| `stabilizerProjection` | `(P_I ∩ n P_J n⁻¹).subgroupOf P_I` | `(M_I ∩ n P_J n⁻¹).subgroupOf M_I` | `p ↦ r_I(p)` |
| `sourceRadicalProjection` | `(P_J ∩ n⁻¹ U_I n).subgroupOf P_J` | `(M_J ∩ n⁻¹ U_I n).subgroupOf M_J` | `p ↦ r_J(p)` |

All public declarations are in
`Langlands.Aubert.General.RationalPointFamily`. The types use the published
`geometricTargetIntersection` and `geometricSourceIntersection` definitions,
including their original conjugation orientations.
`stabilizerProjection_apply` and `sourceRadicalProjection_apply` state the
formulas as equality in the corresponding original Levi subgroup, so their
ambient rational-point formulas follow by coercion.

`stabilizerProjection_surjective` and
`sourceRadicalProjection_surjective` prove surjectivity. The theorems
`map_stabilizer_eq` and `map_sourceRadical_eq` state literal equality of the
image under the original ambient projection with the codomain subgroup in
the table. They retain the exact `subgroupOf` restrictions; they do not merely
identify isomorphic abstract groups.

## Implemented argument

The private `projection_mem_of_closed_stable` helper applies the published
closed stable limit theorem at the identity test scheme. The three standard
subgroup functors are identified with the parabolic, centralizer and
unipotent functors of a chosen cocharacter. The exact rational-point
projection is the dynamic limit by `projection_eq_dynamic_limit`. Since the
point lies in the closed invariant subgroup, its limit lies there as well.
The dynamic point, its limit and its `HasLimit` proof are explicitly typed.

For `projection_mem_conjugate_parabolic`, the standard-cocharacter input
chooses cocharacters for `I` and `J`. The point-normalizer equivalence lifts
`n` without changing its underlying rational point.
`groupHom_cocharacterAut_comp` then realizes the forward conjugate of the
`J` cocharacter by a cocharacter of the same commutative torus. The rational
points of its dynamic parabolic are exactly `n P_J n⁻¹`.
`parabolic_isStable_conjugation`, followed by restriction along the `I`
cocharacter, gives invariance. Its closed affine representative supplies
the closedness needed by the helper. Consequently `r_I` preserves
`n P_J n⁻¹`.

`projection_mem_conjugate_unipotent` uses the same proof with the closed
dynamic unipotent subgroup and `unipotent_isStable_conjugation`. The private
`unipotent_points_conjugate` helper derives the rational-point conjugation
formula from `unipotent_eq_comap_of_iso` and
`rationalPoints_comap_innerIso_inv`. Applying this preservation result with
`I` and `J` exchanged and normalizer point `n⁻¹` gives preservation of
`n⁻¹ U_I n` by `r_J`. Thus neither containment relies on a surviving-orbit
radical assertion.

Each restriction homomorphism uses that containment and the original
projection's homomorphism laws. For surjectivity, a point in the codomain
already belongs to the corresponding Levi. Its Levi inclusion belongs to
the domain, and `IsSemidirectDecomposition.projection_levi` says that its
projection is the original point. The private general group lemma
`map_eq_of_surjective_restriction` converts this surjective restriction and
its pointwise formula into the two image equalities. Keeping that argument
at the level of arbitrary groups avoids unfolding the rational-point
subgroup definitions during kernel checking.

## Declaration dependencies and provenance

This is an internal consequence of published definitions and theorems;
it asserts no independently sourced geometric-lemma proof. The direct
mathematical dependencies are:

| Dependency | Use |
| --- | --- |
| `StandardCocharacterStatement` | Existence of the two cocharacters and all three standard/dynamic subgroup comparisons |
| `normalizerEquiv`, `normalizingAut`, `cocharacterAut`, `groupHom_cocharacterAut_comp` | Realize conjugation by the exact normalizer point through the same torus |
| `Dynamic.rationalPoints_parabolic_conjugate` | Forward parabolic conjugation on actual rational points |
| `Dynamic.unipotent_eq_comap_of_iso`, `SubgroupFunctor.rationalPoints_comap_innerIso_inv` | Forward unipotent conjugation on actual rational points |
| `Dynamic.parabolic_isStable_conjugation`, `Dynamic.unipotent_isStable_conjugation`, `AutomorphicAction.IsStable.restrict`, `AutomorphicAction.restrict_conjugation` | Stability under the selected cocharacter |
| `Dynamic.Affine.isRepresentedBy_parabolicHom`, `Dynamic.Affine.isClosedSubgroup_parabolicHom` and their unipotent counterparts | Closed affine subgroup representatives |
| `Dynamic.hasLimit_limit`, `Dynamic.HasLimit.mem_of_isClosedSubgroup_of_isStable`, `projection_eq_dynamic_limit` | Limit membership and identification with the exact rational projection |
| `IsConnectedReductive.isSeparated` | Separatedness needed by the dynamic projection comparison |
| `IsSemidirectDecomposition.projection_levi` | Original Levi section used in both surjectivity proofs |
| `geometricTargetIntersection`, `geometricSourceIntersection`, subgroup maps and subtypes | Literal domain, codomain and image identities |

The closed stable limit theorem uses closed-immersion lifting from the
punctured affine line, and the standard projection comparison uses the
existing dynamic decomposition and uniqueness of the Levi factor. These
are algebraic group-scheme arguments. The proof bodies above do not invoke
a geometric expansion, adjointness, cuspidal support, character independence
or Langlands classification. In particular they do not use Aubert
Proposition 3.2 or the defective original application to Theorem 3.6.

The import closure is broader than these proof bodies. In particular,
`GeometricK0Target` imports the actual representation-theoretic functors
whose intersection definitions are used here, and
`RationalWeylComparisonTarget` supplies the point-normalizer interface.
Importing those modules does not discharge their representation targets.

## Remaining consumer obligations

This unit establishes the two algebraic projection images. It supplies no
continuity assertion for the restricted maps, rational orbit enumeration,
ordered geometric filtration or normalized graded-piece comparison. It
uses no Coxeter, root-length, finite-length or
`GeometricIntersectionDecompositions` premise. The proper-intersection
comparison still needs its topology and quotient Haar measure hypotheses,
both normalization corrections, the actual distinct-radical modulus
comparison, smooth realization and compact-induction/full-induction
comparison. Neither image identity proves the surviving-orbit radical
statements with their different target subgroups. The exact rational
geometric K0 expansion remains a separate obligation.
