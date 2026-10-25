# Exactness and binary products of refined opposite Jacquet quotients

Author: Worker 430.

This pair states an internal consequence of the existing actual quotient and
map constructions. It contains proposition definitions, not proofs.

`Langlands.Parabolic.NormalizedRefinedOppositeJacquetExactnessStatement`
quantifies over every prime `p`, p-adic field `F`, topological datum `T`, rank
`n`, ordered block shape `B`, and refinement `S : BlockRefinement B`.
The field universe `uF` and the three representation-carrier universes
`uU`, `uV`, and `uW` are independent. There is no positive-rank assumption,
and the zero representations are allowed.

Write `r(ρ) = T.normalizedRefinedOppositeJacquet B S ρ`. Its carrier is the
actual quotient of the carrier of `ρ` by the linear span of
`ρ(u)v - v` for elements of the actual refined opposite unipotent subgroup
of `B.Levi F.Carrier`. The acting group on the quotient is the existing
common refined Levi, `Geometric.refinedLevi F.Carrier B S`.
Normalization multiplies its raw action by the positive half of the
explicit upper full modulus, equivalently the inverse half of the inverse
full modulus. For every input intertwiner `f`, the map in this statement
is precisely `T.normalizedRefinedOppositeJacquetMap B S f`, with
representative formula `[v] ↦ [f(v)]`.

## Actual exactness assertions

`NormalizedRefinedOppositeJacquetInjectionClause` says that an injective
intertwiner `i : ρ → σ` induces an injective map `r(i)` when `σ` is smooth.
The source and target carriers are independently quantified. Smoothness
of the source is not an extra premise: an injection into a smooth
representation already implies it.

`NormalizedRefinedOppositeJacquetRightExactnessClause` uses three
independent carriers and actual intertwiners `i : ρ → σ` and `q : σ → τ`.
If `q` is surjective and the linear range of `i` is the linear kernel of
`q`, then the range of `r(i)` equals the kernel of `r(q)`, and `r(q)` is
surjective. Neither injectivity of `i` nor smoothness is required for
this algebraic right-exactness assertion.

Taken together, these clauses assert preservation of every short exact
sequence with smooth middle representation. They also expose injection
preservation separately, so an application to an actual embedding does
not need to choose an auxiliary cokernel. All assertions concern the
specified actual maps and submodules.

## Actual binary-product equivalence

`NormalizedRefinedOppositeJacquetBinaryProductClause` asserts an actual
equivariant linear equivalence

```text
r(ρ.prod σ) ≃ r(ρ).prod r(σ)
```

whose value on each quotient class is prescribed:

```text
[(u,v)] ↦ ([u],[v]).
```

The product is the componentwise binary product of representations, with
carrier the ordinary product of their vector spaces. The two factors
have independent carrier universes. No smoothness hypothesis is used.
Requiring a representation equivalence includes a linear inverse and
equivariance; the representative formula fixes its forward map.

## Internal provenance and scope

The exact presentation is derived from the published constructors in
`Langlands.Representation.Parabolic.OppositeRefinementFunctors` and
the elementary coinvariant arguments in
`Langlands.Representation.Jacquet.ExactProof`.
The latter proves algebraic surjectivity and middle exactness, and
smooth injection preservation for groups whose finite subsets lie in
compact open subgroups. For the present lower refined radicals,
establishing that finite-containment property is a proof obligation,
rather than an added premise of this statement. The upper refined
radical result in `Parabolic.UnipotentFiniteContainment` and
inverse-transpose transport provide a possible route.

The product comparison is the elementary quotient comparison obtained
from the two projections. Its inverse is induced by the sum of the two
inclusions. The same normalizing character acts on both factors.
This explains the internal algebraic provenance of the asserted
representative formula; this pair does not implement that proof.

This statement asserts no finite composition-series existence,
multiplicity calculation, second adjointness, Jacquet transitivity,
inducing-data recovery, quotient reflection, or classification.
