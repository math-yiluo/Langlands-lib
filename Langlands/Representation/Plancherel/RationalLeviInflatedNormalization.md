# Positive Levi normalization on actual standard rational points

This derived adapter specializes the source covariance API in
`LeviInflatedNormalization` to the literal standard subgroups from
`Langlands.Aubert.General.RationalPointFamily`. The original source is
Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, I.3, printed p.243 (PDF p.9), DOI
10.1017/S1474748003000082. The registered source
`waldspurger-2003-plancherel` has SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Its induction model has positive Levi half-modulus covariance and one open
right stabilizer for each function. This file is an internal specialization
of existing constructions, not an additional theorem quoted from the source.

## Exact retained inputs

The field `k` lies in an arbitrary universe `u`, with `Field`,
`TopologicalSpace`, `T2Space`, `ValuativeRel` and
`IsNonarchimedeanLocalField`. No restriction on its characteristic is made.
The group scheme `G` is affine and connected reductive over `k`; `T` is a
commutative group scheme, `i : T.toGrp ⟶ G` is a displayed maximal split torus,
and the cocharacter `ν` is generic. The existing
`StandardCocharacterStatement` remains an explicit conditional structural
input. A finite subset `I` of the associated simple roots indexes the actual
standard parabolic, Levi and unipotent subgroups.

The ambient group is literally `RationalPoint k G.X`, with the canonical
`Langlands.Aubert.General.RationalPointFamily.pointTopology`, based on
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology`. Local
compactness and `NonarchimedeanGroup` are retained on that exact topology. The
separate
`T2Space k` premise supplies the separation needed by the imported closedness
proof. The representation carrier universe `v` is independent of `u`; input
objects are canonical `SmoothRep.{0, u, v} ℂ (levi i ν I)` and output carriers
lie in `max u v`.

These are conditional actual-point constructions. Neither the standard
cocharacter assertion nor the remaining ambient topological premises are
realized here. The source assumes admissibility, while this function-model
comparison holds for all smooth Levi representations with the displayed
inputs. No admissibility or finite-length preservation, compact picture,
Hermitian pairing or Plancherel theorem is asserted.

## Derived subgroup data and normalization

The local notation `D` denotes the proved
`isSemidirectDecomposition_of_standardCocharacterStatement`, applied to these
exact standard subgroups and structural premises. The local `hU` denotes
`standardUnipotent_isClosed_of_standardCocharacterStatement`. Thus neither
the standard semidirect decomposition nor closedness is an extra input.

`standardLeviInflatedInductionFunctorOfStandardCocharacter` abbreviates the
published `DynamicNormalization.leviTwistedInductionFunctor` at `D` and `hU`:
twist the actual Levi representation by its positive Haar half-character,
inflate by the actual
Levi projection, then take smooth induction from the actual parabolic.

`standardNormalizedInductionLeviIsoOfStandardCocharacter` specializes the
published `DynamicNormalization.normalizedInductionLeviTwistIso`. Its
radical-unimodularity premise is discharged by
`standardUnipotent_isUnimodular_of_standardCocharacterStatement`. That
published theorem follows from compact containment for the actual dynamic
unipotent group and the standard-cocharacter comparison; compact containment
and unimodularity are not additional hypotheses of this adapter. The
resulting isomorphism compares the existing full-parabolic normalized
induction with the positive Levi-twist-before-inflation functor.

The generic component evaluation laws
`normalizedInductionLeviIso_hom_eval` and
`normalizedInductionLeviIso_inv_eval` apply to this specialization and preserve
every function value. They provide the evaluation API without additional
rational-point wrappers.

## Source covariance and actual functions

`standardNormalized_covariant_iff_leviOfStandardCocharacter` identifies
covariance under every actual `p : parabolic i ν I` with
`LeviNormalizedCovariant D hU A f`, for every actual function
`f : RationalPoint k G.X → A`. The right-hand side is exactly

`f(m*u*x) = δ_P(m)^(1/2) • A.representation m (f x)`.

Here the positive factor is the Haar half-character of the actual unipotent
subgroup, evaluated on the actual Levi element. The proof applies the generic
covariance equivalence with the derived standard radical-unimodularity proof.

`standardNormalizedFunctionOfStandardCocharacter` takes that source
covariance, a single open subgroup `K` of the point group, and invariance under
every right multiplication by an element of `K`, uniformly in the function
argument. The generic `leviNormalizedFunctionOf` first constructs the actual
Levi-normalized induced vector. The inverse component of the derived rational
normalization isomorphism then gives an element of the original
full-parabolic normalized induction. Both constituent maps preserve function
values by the generic evaluation laws. The constructor imposes no compact
support condition.
