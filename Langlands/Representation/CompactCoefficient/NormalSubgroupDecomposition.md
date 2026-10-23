# Conditional decomposition from a normal subgroup

This internal construction combines the intrinsic conditional projections,
finite fixed-level support, ambient equivariance, and natural-idempotent
decomposition interfaces. It constructs actual invariant summands in the
ambient representation. Its four analytic inputs remain explicit hypotheses;
it does not prove those inputs or the unconditional Levi quasicuspidal theorem.
The derivation uses no additional literature theorem.

## Parameters and analytic inputs

Let `G` be a topological group and `N` a normal subgroup with its subtype
topology. Assume `NonarchimedeanGroup N` and `WeaklyLocallyCompactSpace N`.
The group universe `uG` and carrier universe `uV` are independent. All smooth
complex representations used in the assembly have carriers in `Type uV`, and
the compact-coefficient classes are indexed at that same carrier universe.
No admissibility, finite length, irreducibility or finite dimension is imposed
on the ambient representation.

The projector construction requires:

1. `hsplit`: for every compact-coefficient class `c` and every smooth
   representation `D` of `N`, its intrinsic `c`-isotypic subrepresentation
   and `c`-annihilator have complementary underlying submodules.
2. `hstrata`: for every compact open subgroup `K` of `N`, the set of
   compact-coefficient classes having a nonzero `K`-fixed vector is finite.

The decomposition theorem additionally requires:

3. `hcompact`: for every smooth `D` of `N`, its intrinsic total isotypic
   subrepresentation has compact smooth-dual coefficients.
4. `hexhaust`: for every smooth `D` of `N` with compact smooth-dual
   coefficients, its intrinsic total isotypic subrepresentation is top.

These are quantified hypotheses, not conclusions obtained from the topology.
The universe of classes matches the carrier universe in both total-isotypic
hypotheses, so no resizing or universe-exhaustion claim is implicit.

## Projector and compatibility

`SmoothRep.restrictSubrepresentation N S` views an actual ambient invariant
subspace `S` as a subrepresentation of `SmoothRep.restrictSubgroup N A`.
It retains exactly `S.toSubmodule`; invariance follows by evaluating ambient
invariance at the subgroup inclusion. This definition itself needs neither
normality nor a topological-group assumption.

`CompactCoefficientClass.normalSubgroupProjector N hsplit hstrata A` takes
the conditional projection onto each intrinsic isotypic component of the
restriction of `A` to `N`. Its kernel is the corresponding annihilator.
The finite-stratum theorem makes these components pointwise finite. Their
idempotence and exact ranges and kernels are supplied by the conditional
projection laws, so `ambientTotalProjector` upgrades their sum to an actual
ambient intertwiner. Ambient equivariance is inherited from its explicit
inverse-conjugation and class-permutation argument.

The module proves:

- `normalSubgroupProjector_idempotent`: the ambient projector is idempotent.
- `normalSubgroupProjector_range`: restricting its actual ambient range
  gives exactly the intrinsic total isotypic subrepresentation of `A|N`.
- `normalSubgroupProjector_natural`: for every ambient intertwiner `f`,
  `e B (f v) = f (e A v)`.
- `normalSubgroupProjector_eq_self`: with `hexhaust`, the projector fixes
  every vector of any ambient object whose restriction has compact
  smooth-dual coefficients.

Ordered orthogonality follows from the published separation of distinct
classes. The range identity follows from the supremum-of-ranges law and
injectivity of the underlying-submodule map. Naturality follows from the
ambient-total law. For the identity-on-compact-objects result, exhaustion
makes the range top. Every vector is therefore the image of some vector,
and idempotence shows that it is fixed.

## Actual invariant decomposition

`decomposition_of_normalSubgroup_compactCoefficients` concludes that every
smooth complex representation `A` of `G` has actual subrepresentations `S,Q`
with complementary underlying submodules, such that:

- The restriction of the actual representation on `S` to `N` has compact
  smooth-dual coefficients.
- Every actual smooth ambient subquotient `D` of the representation on `Q`
  whose restriction has compact smooth-dual coefficients is a subsingleton.

The proof applies `SmoothRep.decomposition_of_natural_idempotent` to the
constructed family and the property of having compact coefficients after
restriction. For the image condition, restriction of the actual ambient
range has the same submodule as the intrinsic total isotypic part, so the
range equality rewrites the goal to `hcompact`. The action on that submodule
is the original action restricted to `N`, by definition. The fixing condition
is `normalSubgroupProjector_eq_self`. The imported natural-idempotent theorem
chooses the actual range and kernel and uses naturality through inclusions,
quotient maps and isomorphisms to establish the full subquotient conclusion.

To obtain the Levi quasicuspidal decomposition one must still prove the
four analytic inputs for the actual determinant-unit subgroup, supply its
topological instances, and identify compact coefficients on the restriction
with quasicuspidality through the Harish-Chandra criterion. None of those
unconditional inputs is asserted by this module.
