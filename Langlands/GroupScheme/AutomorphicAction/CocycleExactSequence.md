# Exactness for actual nonabelian cocycles

This is an internal construction from the actual relative cocycles in
`AutomorphicAction/Cocycles`, equivariance in `Dynamic/ActionFunctoriality`,
and the represented kernel of a group-scheme homomorphism. It supplies one
exactness step for a later induction on unipotent groups. All schemes have an
arbitrary common universe `u`.

Let `S` be any base scheme, let `H`, `N`, `G`, and `Q` be group schemes over
`S`, and fix automorphic actions `aN`, `a`, and `aQ` of `H` on the last three
groups. The parameter `T` is an arbitrary scheme over `S`. A cocycle is an
actual morphism `T × H → G`, satisfying its identities on all test schemes;
no construction here replaces it by a function on rational points.

## Pushforward and conjugation

For an equivariant group homomorphism `q : G ⟶ Q`, `Cocycle.map` composes the
actual cocycle morphism with `q`. Its identity and multiplication laws follow
from those of the original cocycle, the group-homomorphism laws, and
equivariance. `eval_map` gives the corresponding equation on every test.

`map_trivial`, `map_conjugate`, and `map_coboundary` show that pushforward
preserves the trivial cocycle, commutes with conjugation, and sends the
coboundary of `g : T → G` to the coboundary of `q(g)`. The convention inherited
from `Cocycles` is

```text
conjugate(g,c)(b,h) = g(b) c(b,h) a(h,g(b))⁻¹,
coboundary(g)(b,h) = g(b) a(h,g(b))⁻¹.
```

`conjugate_coboundary` identifies conjugating the coboundary of `g'` by `g`
with the coboundary of `g g'`. The two inverse-conjugation lemmas follow
directly from the published multiplication law for conjugation.

## Actual factorization through the kernel

Fix an equivariant homomorphism `n : N ⟶ G` whose underlying arrow is a
monomorphism. If the actual cocycle morphism `c.hom` belongs to the represented
range of `n` on `T × H`, `Cocycle.lift` chooses a factorization of that
morphism through `N`. Applying `n` to the required cocycle identities reduces
them to those of `c`, using equivariance for multiplication; monicity then
gives the identities in `N`.

`lift_map` proves that pushing this lifted cocycle along `n` recovers `c`.
`lift_unique` proves uniqueness among cocycles of `N` with that pushforward.
The range premise is membership of an actual morphism at the product test
scheme, not a premise about a chosen collection of field-valued points.

Assume now that

```text
SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q).
```

If `c.map q hq` is the trivial cocycle, equality of its actual morphism with
the identity morphism shows that `c.hom` belongs to the represented kernel.
`hom_mem_range_of_map_trivial` transfers this membership to the range of `n`.
The entry definition `Cocycle.kernelLift` applies `lift` to that membership
and produces an actual cocycle for the supplied action `aN`.
`kernelLift_map` proves exact recovery under pushforward along `n`.

## Recombining a quotient correction and a kernel correction

`exists_coboundary_of_map_eq_coboundary` retains all the data and hypotheses
above. It additionally assumes a specified `g : T → G` such that
`c.map q hq = aQ.coboundary (g ≫ q.hom.hom)`, and assumes that every actual
`aN`-cocycle with parameter `T` is a coboundary of a morphism `T → N`.
It concludes that there is such a morphism `v` with

```text
c = a.coboundary (g * (v ≫ n.hom.hom)).
```

The proof conjugates `c` by `g⁻¹`. Pushforward compatibility and the assumed
quotient equation make its image trivial. `kernelLift` factors the residual
cocycle through `N`; the kernel-coboundary premise supplies `v`.
Pushing that equality into `G` and conjugating back by `g` gives the displayed
formula. This uses the original actions throughout; no centrality or
commutativity hypothesis is needed.

## Provenance and scope

Every construction and proof here is a formal consequence of the imported
definitions and their group identities. No external theorem is invoked as
an additional premise or cited as the result proved here.

The file imposes no field, characteristic, smoothness, affineness, or
splitness assumptions. The equation identifying the represented kernel is
explicit data. Neither a categorical quotient nor surjectivity of `q` is
needed for this conditional exactness step. Existence of a lift of an
arbitrary quotient point, triviality of the kernel cocycles, structural
unipotent quotients, and maximal-torus conjugacy remain separate obligations.
