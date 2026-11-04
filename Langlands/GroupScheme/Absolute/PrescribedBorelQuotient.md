# Proper homogeneous quotients for a prescribed Borel

Worker 1547, adapting Worker 1396's published orbit-stabilizer proof,
following Worker 317's proposed prescribed-Borel route.

This is an internal generalization of
`someBorelQuotientProper_of_prerequisites` from
`Absolute.BorelProperQuotientReduction`. The Borel is now an input, so its
actual embedding is retained. The module proves no fixed-point theorem and
does not prove positive-root uniqueness.

Over every algebraically closed field `k : Type u`, let `G` be a smooth,
affine, connected group scheme and let `i : B → G` satisfy the unchanged
`IsBorelSubgroup i`. There is no restriction on characteristic or on the
chosen Borel. In particular, a factorization of a specified torus through
this embedding can be retained by a caller.

`IsBorelSubgroup.quotient_isProper_of_prerequisites` assumes the three
published proposition targets `GeneralLinearSolvableStabilizerStatement`,
`ClosedOrbitStatement` and `SolvableProperFixedPointStatement`. For any
actual relative scheme `Q` and morphism `q : G.X → Q`, assume the structure
map of `Q` is separated, locally of finite type and quasi-compact, and
`q.left` is smooth, surjective and quasi-compact. Assume also, on every
relative scheme test `T`, the exact right-coset criterion

```lean
g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T
```

The theorem concludes `IsProper Q.hom`. The criterion includes nonreduced
and nonaffine tests; it is not merely an equality on rational points.

The implemented proof is the published proof with its internal Borel
choice removed. Embed `G` as a closed subgroup of a general linear group,
choose the proper flag scheme supplied by the stabilizer proposition,
and take a reduced closed orbit. The fixed-point proposition applied to
the supplied `B` gives a rational point on this proper orbit fixed by `B`
on all tests. Form its closed stabilizer and its reduced identity
component. The flag-stabilizer proposition makes that component solvable,
and maximality of this very `B` identifies their ranges. The existing
orbit-map flatness theorem and finite-index quotient properness transfer
then imply properness of the supplied `Q`. All stabilizers and range
equalities are scheme-theoretic. No Borel conjugacy is used.

`IsBorelSubgroup.quotient_isProper_of_solvableProperFixedPoint` discharges
the first two proposition inputs with the published theorems
`generalLinearSolvableStabilizer` and `closedOrbit`. The solvable proper
fixed-point statement remains an explicit premise.

`IsBorelSubgroup.exists_properQuotient_of_solvableProperFixedPoint`
combines this specialization with `smoothSubgroupQuotientExistence`,
applied to the same smooth closed embedding `i`. It supplies an actual
`Q`, projection `q`, properness of `Q`, smoothness, surjectivity and
quasi-compactness of `q`, and the same exact fiber criterion on every
test. No quotient-existence premise remains in this last theorem.

`IsBorelSubgroup.ProperQuotientData i` stores this construction as actual
data. Its fields are the relative scheme `quotient`, its `projection` from
`G.X`, proofs `proper`, `smooth`, `surjective` and `quasiCompact` of the
properties just stated, and `fibers`, the exact coset criterion above on
every relative scheme test. The data type itself records the supplied
embedding `i`; it does not assert that `i` is Borel.

`IsBorelSubgroup.properQuotientData_of_solvableProperFixedPoint` uses
classical choice on the existence theorem to produce these data from
`hB : IsBorelSubgroup i` and the same fixed-point premise. It preserves the
specified embedding and makes no canonical-choice or uniqueness claim.

## Provenance and remaining obligations

This module is derived from the named published constructions. Its main
proof adapts Worker 1396's proof in `BorelProperQuotientReduction`, retaining
that contribution's orbit-stabilizer argument and using its imported
stabilizer and reduced-subgroup results. The specialization and existence
assembly reuse proved Library theorems by their Lean names. No new
external mathematical assertion is assumed beyond the explicit
`SolvableProperFixedPointStatement` premise.

The module does not discharge that premise, torus conjugacy, a projective
fixed-point dimension bound, the curve-to-root comparison, or
`RankOnePositiveRootUniquenessStatement`. It establishes the prescribed
Borel quotient construction needed to formulate those remaining steps.
