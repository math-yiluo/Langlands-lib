# Geometry and scalar points of the actual multiplicative group

Author: Worker 487.

This module supplies the geometric consequences of
`Langlands.GroupScheme.Gm.relativeLaurentIso`, together with scalar points of the
existing multiplicative group scheme and an equality criterion for its
morphisms. Every declaration is in `Langlands.GroupScheme.Gm`. Throughout, the
source is the actual published `GroupScheme.Gm`, constructed by base change
from the integral Laurent spectrum.

## Internal provenance

These are internal supporting constructions for the relative Laurent model,
derived from `Langlands.GroupScheme.MultiplicativeLaurent`, the published
`Gm.affinePointsEquiv`, and Mathlib's finite-type, reducedness, and closed-point
results. The module makes no independent external-literature claim.
In particular, the proof uses
`AddMonoidAlgebra.finiteType_of_fg`,
`LocallyOfFiniteType.jacobsonSpace`, `closure_closedPoints`,
`residueFieldIsoBase`, `pointOfClosedPoint`,
`pointOfClosedPoint_comp`, and `ext_of_fromSpecResidueField_eq`.
The scalar convention comes directly from the published units equivalence.

## Finite type and reducedness

For any `R : CommRingCat`, `relativeLaurent_locallyOfFiniteType` proves that the
coefficient structural map of `relativeLaurent R` is locally of finite type.
The affine criterion reduces this to finite type of the algebra
`LaurentPolynomial R`. This is the additive monoid algebra on the finitely
generated additive monoid of integers, so Mathlib's finite-type instance applies.
The instance `Gm.locallyOfFiniteType R` transfers the result to
`(GroupScheme.Gm (Spec R)).X.hom` using the triangle of the proved isomorphism
`relativeLaurentIso R`. No nontriviality or field assumption on `R` is required.

For any field `k`, `isReduced_field k` proves that the underlying scheme of
`GroupScheme.Gm (Spec (CommRingCat.of k))` is reduced.
The Laurent ring over `k` is a domain by Mathlib's monoid-algebra instance;
its spectrum is therefore reduced. The underlying isomorphism of the relative
model is an open immersion, so `isReduced_of_isOpenImmersion` transfers
reducedness to the actual group scheme. Algebraic closedness is not needed here.

## Scalar points

For `a : Rˣ`, `scalarPoint R a` is the morphism

```text
Over.mk (𝟙 (Spec R)) ⟶ (GroupScheme.Gm (Spec R)).X
```

obtained by applying the inverse of `affinePointsEquiv (𝟙 (Spec R))` to `a`.
The lemmas `affinePointsEquiv_scalarPoint` and
`scalarPoint_affinePointsEquiv` are its two inverse identities.
Thus these are the scalar-unit points already specified by the existing
group scheme's affine point API. The imported coordinate-compatibility theorem
identifies their Laurent coordinate with the supplied unit.

## Equality from geometric points

Let `k` be an algebraically closed field and let
`Y : Over (Spec (CommRingCat.of k))` have separated structural morphism.
For two morphisms

```text
f g : (GroupScheme.Gm (Spec (CommRingCat.of k))).X ⟶ Y,
```

`hom_ext_kpoints` proves `f = g` provided `x ≫ f = x ≫ g` for every morphism
`x` from `Over.mk (𝟙 (Spec (CommRingCat.of k)))` to the source.
There is no finite-type assumption on `Y`.

The implemented proof first obtains a Jacobson space from the locally
finite-type source, so its closed points are dense. At each closed point,
`residueFieldIsoBase` identifies its residue field with `k`, and
`pointOfClosedPoint` gives a morphism over the identity base map.
The hypothesis gives equality after this morphism. Cancelling the spectrum
map of the residue-field isomorphism gives equality after the canonical
residue-field point. Finally, `ext_of_fromSpecResidueField_eq` uses this
equality on the dense closed points, the reduced source, the separated target,
and the two structure triangles to prove equality of the scheme morphisms.
Extensionality in the over category finishes the result.

`hom_ext_scalarUnits` restates the hypothesis using
`scalarPoint (CommRingCat.of k) a` for every `a : kˣ`.
It follows from `hom_ext_kpoints` and the inverse identity for `scalarPoint`.

For a group scheme `G` over the same base with separated structural morphism,
`cocharacter_ext_scalarUnits` applies this criterion to the underlying
morphisms of

```text
f g : (GroupScheme.Gm (Spec (CommRingCat.of k))).toGrp ⟶ G.
```

If their composites with every scalar-unit point agree, the two actual
cocharacters are equal. The proof uses `Grp.hom_ext` after the scheme-level
criterion. Neither this result nor the earlier criterion deduces scheme
equality from a bare bijection of point sets; reducedness, closed-point density,
and separation enter the proof explicitly.
