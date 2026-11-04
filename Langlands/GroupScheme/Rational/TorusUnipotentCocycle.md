# Torus cocycles in split unipotent groups from structural inputs

This internal deduction assembles dimension induction for actual rational
cocycles of a torus acting on a smooth connected affine split unipotent
group. All schemes and fields have arbitrary common universe `u`.

The main theorem and entry construction retain these three explicit
proposition parameters:

- `SplitUnipotentStableVectorSubgroupStatement`;
- `TorusVectorActionLinearizationStatement`;
- `SplitUnipotentAffineTorsorStatement`.

The entry `RelativeRoot.torusUnipotentCocycleConjugator` constructs an actual
rational point conditional on these parameters. The accompanying equality
theorem proves that its coboundary is the given actual cocycle. None of the
three proposition parameters is proved here.

## General cocycle and quotient lemmas

`AutomorphicAction.Cocycle.eq_trivial_of_range_id_eq_bot` works over any
base scheme and for any relative parameter scheme. The identity-range
condition says that the whole target group is trivial on every test.
Applying it to the actual cocycle morphism on the product test scheme
shows that the morphism is the identity, hence the cocycle is trivial.

`RelativeRoot.IsFppfQuotient.local_lifts` also works over any base. Given
any test point `y : T → Q` of a represented fppf quotient `q : U → Q`, it
forms the actual scheme pullback of `q` along `y`. Its projection to `T`
is flat, surjective and locally of finite presentation by base change,
and the other projection is a lift of `y` after this cover. This proves
local lifting on arbitrary test schemes; it does not assert surjectivity
on the point group of each original test.

`exists_coboundary_of_isTorus_vector_kernel` specializes actual nonabelian
cocycle exactness to a torus acting on a vector kernel over a field. Its
inputs are equivariant maps `z : V → U` and `q : U → Q`, monicity of `z`,
affineness of `V`, equality of the represented range of `z` with the
kernel range of `q`, and scalar-linear natural vector coordinates for
the action on `V`. For a specified rational point `g` of `U`, if the
quotient cocycle is the coboundary of `q(g)`, it constructs a rational
point `v` of `V` with

```text
c = a.coboundary (g * (v ≫ z.hom.hom)).
```

The proof applies `Cocycle.exists_coboundary_of_map_eq_coboundary` and
discharges its kernel-coboundary premise with the published
`RelativeRoot.exists_coboundary_of_isTorus`. The acting torus need not
be split. This lemma assumes no centrality of the kernel.

## The dimension induction

Let `k` be any field, let `H` be any `k`-torus, and let `U` be smooth,
connected and affine over `k`. Assume both `IsUnipotent U` in the
Library's representation convention and `IsSplitUnipotent U`, which
means a finite represented fppf normal series with additive-group
quotients. Fix an actual action `a : AutomorphicAction H U` and an actual
cocycle with parameter `Spec k`.

`exists_coboundary_of_split_unipotent_of_structuralStatements` proves
that this cocycle is a rational coboundary, conditional on the three
proposition parameters listed above. The proof first obtains a constant
finite smooth relative dimension of `U`, using its connectedness.
It then performs strong induction on that dimension, allowing the
group, action and cocycle to vary.

If the identity range is bottom, the general triviality lemma makes
the cocycle the coboundary of the identity point.
Otherwise the stable-vector parameter supplies an actual positive
dimensional smooth central vector subgroup `z : V → U`, its actual
equivariant action, its splitness and unipotence, natural vector
coordinates of dimension `n`, and its smooth relative dimension `n`.
The torus's smoothness and affineness discharge the corresponding
acting-group hypotheses of that parameter.

The proof constructs an actual affine normal quotient `q : U → Q` with
the descended action by applying
`Chevalley.exists_unipotentNormalQuotientOfFieldExtension` over the
algebraic closure of `k`. Its closed-orbit input is the published proof
`unipotentAffineOrbitClosed`; its field-extension inputs are the
published unipotence-preservation proofs for `U` and the supplied `V`.
The centrality of `z` gives normality. The quotient construction provides
smoothness, connectedness, unipotence, exact fppf kernel, equivariance,
and the dimension equation `d = n + m` with `m < d`.
No quotient-existence, quotient-affineness or dimension-additivity
proposition is assumed in addition to the three named parameters.

The proved `IsSplitUnipotent.of_surjective_to_smooth_affine`, applied to
`q`, gives split unipotence of `Q`. It uses the published image and
split-series proofs, so quotient splitness is not a retained proposition
parameter. Strong induction now trivializes the
pushed-forward cocycle in `Q`, giving a rational correction point `y`.
The affine-torsor parameter, through
`HomogeneousQuotient.fppf_section_of_split_unipotent_torsors`, supplies
an actual scheme section of `q`. Composing `y` with that section gives
the required rational lift `g`.

Finally the linearization parameter supplies natural scalar-linear
coordinates of the same dimension `n` for the actual torus action on
`V`. These coordinates may differ from those supplied by the
stable-vector parameter. The vector-kernel exactness lemma corrects
`g` by a point of `V` and proves equality with the original actual
cocycle morphism.

## The chosen point and retained obligations

`torusUnipotentCocycleConjugator` chooses the rational point from the
existence proof. The theorem
`cocycle_eq_coboundary_of_split_unipotent_of_structuralStatements`
proves its exact coboundary equation. The conjugation convention is
the one in `AutomorphicAction/Cocycles`:
`coboundary(g)(h) = g a(h,g)⁻¹`.

The base field, its characteristic and its perfection are unrestricted;
the torus may be nonsplit and may have dimension zero. Identities are
equalities of actual cocycle morphisms and therefore hold on all scheme
tests. The constructed quotient section is a scheme morphism; it is
not required to preserve multiplication.

The proof is an internal deduction from the imported definitions and
published proofs, with the three structural propositions retained
verbatim as explicit hypotheses. Their own documentation records
their external mathematical provenance. This file does not discharge
those propositions, handle a nonsplit unipotent target, prove torus
lift existence across an extension, or prove maximal-torus conjugacy.
