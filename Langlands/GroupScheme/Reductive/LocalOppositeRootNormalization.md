# Normalized opposite-root Gauss relations over local rings

This internally derived module constructs the Gauss and coordinate-separation
inputs used by `OppositePowerRigidity` for actual opposite root parametrizations
over arbitrary local rings. It also retains the Weyl reflection identity for the
same normalization. It is a prerequisite for the isogeny rigidity proof; it does
not assert or prove the full torus-conjugacy statement.

The construction uses the published actual rank-one centralizer, ring cell
calculus, pointed etale unit-cell construction and dual-number normalization
descent. Its provenance is the composition of these Library results, with the
all-test point interfaces of `LocalSplitCell`. It makes no additional claim about
the original literature underlying those imported results.

`OppositePower.HasCorootGaussRelation i nu xp xm` is a proposition over a
commutative ring `R` and a finite coordinate set `I`. For every scheme `Z` over
`Spec R`, global sections `x,y`, and unit `d` whose value is `1+x*y`, it asserts

```text
xp(x) xm(y) = xm(d⁻¹ y) i(nu(d)) xp(d⁻¹ x).
```

Here `nu(d)` is the actual coordinate exponent-cocharacter point
`cocharPoint nu Z d`. Every product and equality is in the group of morphisms
from `Z` to the supplied group scheme. In particular, the quantification includes
nonreduced tests. Forgetting the prescribed middle factor gives
`HasGaussRelation`. The last clause of the existing `RankOneLaws` gives this
coroot formula directly.

`HasCorootGaussRelation.of_baseChange` descends the formula along an algebra base
map with faithful pullback on over-categories. For an original test `Z`, it uses
the pulled-back test and the counit from its image to `Z`. That counit is an
epimorphism. Naturality of root points, cocharacter points and the
base-change-points equivalences transports the assumed formula; cancellation of
the counit gives the original equality. Equality is not tested only over fields.

Composition with any group morphism preserves the coroot formula.
`SeparatesPositive.comp` preserves positive-coordinate separation under an
inclusion whose underlying morphism in the over-category is monomorphic.
`SeparatesPositive.scaleNegative` preserves separation after any scalar
rescaling of the negative coordinate; this transfer itself needs no unit
hypothesis.

For actual `RingRootCell.WeylData W`, `pb_cβ_eq_baseScalar` identifies the
pullback of the stored beta section with the base scalar of `W.betaUnit`.
The proof uses the actual `GammaSpecIso` and naturality of base scalars.
The ring-calculus relation then gives `hasGaussRelation` for
`W.xp` and `scaleHom W.betaUnit` followed by `W.xm`, when `W.G` is affine.
Injectivity of the rank-one cell gives `separatesPositive` for this pair.

The subsequent adapters concern the actual relative centralizer of a
cocharacter `mu` in a reductive group over a local ring. Their input consists of
a closed, fibrewise maximal coordinate split torus `i`, its fibrewise root
datum `P`, a root `a`, actual opposite root parametrizations `xp,xm`, and an
exponent `mu` vanishing on `P.root a` and on no other roots except its opposite.
The intermediate adapters also take the existing affine etale unit-cell data.

`affineEtale_hasCorootGaussRelation` applies the normalized ring relation over
that data's coefficient ring. The Weyl data's cocharacter is definitionally the
supplied exponent cocharacter of `P.coroot a`; `cocharPoint_eq_comp` identifies
its pointwise middle factor with the coroot formula above.
`scalar_hasCorootGaussRelation` descends this formula for any original scalar
whose coefficient-ring image is `W.betaUnit`. The coefficient projection is
etale and surjective, which supplies faithful pullback, and base change of
`scaleHom` identifies the negative coordinate.

`exists_gauss_normalizing_scalar` uses the dual-number factorization to obtain
the original normalization scalar `c`. The imported unit theorem proves `c`
is a unit, and its coefficient-ring image is `W.betaUnit⁻¹`. Taking the inverse
of that unit therefore gives a scalar `d` with image `W.betaUnit`.
The Gauss descent adapter and the existing
`scalarWeylPoint_isNormalizing` use exactly this same `d`. The local version
constructs the pointed etale unit-cell data at the closed point and obtains the
required dual-number factorization from the actual rank-one cell.

`LocalSplitCell.exists_unit_oppositeNormalization` is the ambient conclusion.
It assumes a commutative local ring `R`, a reductive affine group `G`, a closed
fibrewise maximal coordinate split torus `i`, a supplied fibrewise root datum
`P`, and parametrizations of the root `P.root a` and its negative. For every such
pair it gives a unit `d : Rˣ` such that all three assertions hold:

- The pair `xp`, `scaleHom d` followed by `xm` satisfies
  `HasCorootGaussRelation i (P.coroot a)`.
- The same pair satisfies `SeparatesPositive i`.
- Its Weyl product normalizes the torus with exponent action `P.reflection a`.

The proof chooses a cocharacter whose vanishing roots are precisely the chosen
opposite pair and applies the simultaneous normalization in its actual
rank-one centralizer. It transfers the Gauss relation through the centralizer
inclusion. The centralizer's own open cell separates coordinates; scaling the
negative factor and composing with its closed ambient inclusion gives ambient
positive-coordinate separation. Finally the same inclusion transfers the
normalizing-point identity to the desired Weyl-point identity.

No hypothesis that `R` is reduced, no assumption that the rank-one triple cell
is open in the full ambient group, and no field-point equality criterion is
used. The finite and reduced root-datum properties needed to choose the
centralizer cocharacter follow from `hP`; they are not reducedness hypotheses
on the base ring. Construction of arbitrary-isogeny root restrictions,
their power degrees and unit coefficients, the torus root-value lift, and
assembly of the full rigidity theorem remain separate obligations.
