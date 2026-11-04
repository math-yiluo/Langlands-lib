# Renard's radical weights and simple indivisible roots

`Langlands.GroupScheme.RenardRootConventionStatement` is a Prop-valued structural
comparison target. This file supplies its statement; it supplies no proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, V.3.4 on printed p.110/PDF p.116 and V.3.12
on printed p.112/PDF p.118. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, with SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.14–V.3.15, printed p.113/PDF p.119, motivate its later use for restricted
simple roots and their root-combination cones.

In V.3.4, Renard writes `Σ′(A)` for the nonzero Lie roots, `Σ(A)` for those
roots indivisible within that root set, `Σ′(P)` for the roots occurring in the
unipotent radical, and `Σ(P)` for their reduced positive part. In V.3.12,
`Δ∅` is the simple system of the reduced positive roots for the chosen minimal
parabolic. Divisibility here concerns the actual root set, rather than
primitivity in the entire character lattice.

The target is a derived comparison with these conventions in the common
group-scheme framework. It quantifies over every field `k : Type u`, connected
reductive group scheme `G` over `Spec k`, maximal split torus inclusion
`i : T → G`, and generic cocharacter `ν` of `T`. The source's nonarchimedean
local-field setting is thus generalized explicitly to arbitrary fields. There
is no characteristic-zero or perfectness assumption, no assumption that `G`
is split, and no restriction to a matrix group. The affine instance is
obtained from connected reductivity. Genericity means that every relative
root pairs nontrivially with `ν`.

For these actual objects, the proposition forms four local sets:

1. `U` is `Dynamic.unipotent (groupHom ν ≫ i)`, the actual dynamic unipotent
   subgroup functor.
2. `pos` consists of the nonzero characters in
   `RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation i) U`.
   The published support detects a nonzero vector in the ambient Lie algebra
   that lies in both the action weight space and the tangent image of `U`.
3. `redPos` is `RelativeRoot.indivisibleRoots i ∩ pos`. The published
   indivisibility predicate excludes equality `α = m • β` for every actual
   relative root `β` and every natural number `m > 1`.
4. `simple` consists of the elements of `redPos` that cannot be expressed as
   a sum of two elements of `redPos`.

The asserted conjunction is precisely:

- `pos = positiveRelativeRoots i ν`;
- `redPos = RelativeRoot.indivisiblePositiveRoots i ν`;
- `redPos = reducedPositiveRelativeRoots i ν`;
- `simple = simpleRelativeRoots i ν`.

The first equality compares actual radical Lie weights with cocharacter
positivity in the ambient relative roots. The next two identify the
source's indivisible positive roots with the two published implementations:
`RootProductStatement` tests integral divisibility before positivity, while
`RelativeWeylCoxeterStatement` starts with positive roots and excludes
multiples of order at least two. The last equality compares indecomposability
within the reduced positive set with the published `simpleRelativeRoots`,
which tests sums in the full, possibly nonreduced, positive root set.
These are equalities of subsets of the actual character lattice of `T`.
For rank zero, the equalities include the empty root sets.

This target introduces no parallel root datum, chosen reflection system or
assumed root decomposition. Its only new declaration is the proposition;
the intermediate sets are local lets. It does not identify every indivisible
positive root as simple: indecomposability remains an additional condition.
In a reduced system of type A2, the sum of the two simple roots is itself
indivisible and positive but is decomposable.

The root-system structural arguments and the dynamic-radical weight
comparison remain proof obligations. This statement neither proves that the
dynamic parabolic is minimal nor constructs compatible presentations for
every specified parabolic, Levi and split component. Independence of
restricted roots and cones across such presentations, the source's central
direction decompositions, and the representation-theoretic temperedness
criterion remain separate obligations. A proof of this proposition can
serve those consumers only after independent acceptance and publication.
