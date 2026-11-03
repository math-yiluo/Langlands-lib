# Descent of actual fixed-torus dynamic presentations

This is an internal derived construction by Worker 146. It uses the published
fpqc reflection development of Worker 1358, the actual cocharacter pullback map
of Worker 1272, and the split-torus lattice equivalence.

Let `k` and `K` be fields in universe `u`, with any `k`-algebra structure on `K`.
Let `G` and `P` be group schemes over `Spec k`, assume that the underlying
scheme of `G` is affine, and let `i : P ⟶ G` be monic on underlying schemes.
Fix a commutative group scheme `T` over `k` and an actual homomorphism
`j : T.toGrp ⟶ G`. Write `b = algebraBaseMap k K`.

For every actual integral cocharacter `ν : cocharacterLattice T`,
`range_eq_parabolic_iff_baseChange` proves that

```text
range i = Dynamic.parabolic (groupHom ν ≫ j)
```

holds if and only if

```text
range (baseChange(b).map i) =
  Dynamic.parabolic
    (groupHom (cocharacterLattice.baseChange b T ν) ≫ baseChange(b).map j).
```

These are equalities of subgroup functors on all test schemes over the respective
fields. Neither equality is restricted to field-valued, affine or reduced tests.
This first equivalence does not require splitness or reductivity.

`FixedTorusDynamicPresentations T j i` is the subtype of the actual cocharacter
lattice consisting of cocharacters satisfying the first equality. Under the
additional hypothesis `hT : IsSplitTorus T.toGrp`,
`fixedTorusDynamicPresentationBaseChangeEquiv` constructs an equivalence between
this type and the corresponding type over `K`. Its forward map is the canonical
actual cocharacter pullback, and its inverse is the inverse of
`cocharacterLattice.baseChangeEquiv b T hT`. Thus every presentation after
extension descends to a unique cocharacter presenting the original subgroup.
The theorem `exists_range_eq_parabolic_iff_baseChange` records the resulting
equivalence of existence.

The torus map `j` need not be monic or maximal. There are no finite type,
smoothness, connectedness, characteristic, separability or finite-extension
hypotheses. For the equivalence of presentation types, splitness is the stated
extra hypothesis. Empty and rank-zero split tori are included.

## Implemented argument

`Dynamic.baseChangeCocharacter_comp` first expresses the functoriality of actual
cocharacter pullback under postcomposition by the given `j`. The published
`cocharacterLattice.groupHom_baseChange_dynamic` identifies the lattice map with
this same pullback. The dynamic parabolic base-change theorem therefore
identifies the right-hand dynamic subgroup with the base change of the original
one. The range base-change theorem makes the same identification for `i`.

The field extension map `b` is flat and surjective by faithful flatness of the
algebra map, and is quasi-compact as a morphism between affine schemes. Equality
of the two original subgroup functors implies equality after pullback by
functoriality. For the converse, the range of `i` is represented by that monic
homomorphism, while
`Dynamic.Affine.isRepresentedBy_parabolicHom` represents the dynamic parabolic
of an affine ambient group. The published fpqc theorem
`SubgroupFunctor.eq_of_isRepresentedBy_baseChange_eq` reflects their equality.
Its descent argument applies to arbitrary test schemes.

For split `T`, the published additive lattice equivalence supplies the inverse
on underlying cocharacters. The preceding equality equivalence supplies the
subtype properties in both directions. The two inverse laws follow from the
additive equivalence's inverse laws and subtype extensionality. Finally, an
extended presentation is pulled back by this inverse to prove the existence
equivalence.

## Provenance and remaining scope

This adapter is derived solely from the imported, proved Library constructions;
it introduces no separate literature assertion or classification assumption.
It can descend an already established fixed-torus presentation, including one
over an algebraic closure. It does not construct such a presentation from
geometric parabolicity. The unconditional geometric classification required by
`SplitParabolicCocharacterStatement` remains a separate obligation.
