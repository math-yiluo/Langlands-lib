# Normality of the actual simply connected image and zero-subgroup products

This derived construction lifts ambient conjugation to the supplied simply
connected derived cover. It reuses the published normality of its actual rational-point image
and shows that the joins defining the unramified and base-field zero subgroups
are their stated product sets. It constructs a surjective multiplication map
from the base-field factors to the actual zero subgroup.

## Scope and provenance

The generic conjugation construction is over an arbitrary field `k : Type u`.
It uses `h : IsSimplyConnectedDerivedCover d π` for the supplied actual maps
`π : C → D` and `d : D → G`. The initial normal-subgroup-functor identity
is valid over every scheme base. The zero-subgroup corollaries specialize to
every nonarchimedean local field `F` of either characteristic, at arbitrary
universe `u`, with the existing `UnramifiedZeroDatum` and `ZeroSubgroupDatum`.

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
The original Definition 2.6.20, Fact 2.6.21 and Definition 2.6.23, printed
page 104 / PDF page 135, and Lemma 2.6.24 with its proof, printed
pages 104–105 / PDF pages 135–136, were read directly. They define the simply
connected image, explain morphism compatibility through lifts, and use
normality of that image in the construction of the zero subgroup.

The implemented proof specializes the lifting idea to actual automorphisms
of the represented derived subgroup. It reuses the published cover comparison
`IsSimplyConnectedCover.isoOver`, which follows from the cover's universal
property. It needs no lifting theorem for arbitrary noninvertible morphisms.
The normality and product consequences are derived results on the existing
subgroups; no additional numbered source assertion is claimed.

The 1 November 2024 corrections, registered as
`kaletha-prasad-2024-corrections`, PDF page 25, insert Henselian and
perfect-residue-field assumptions before Definition 2.6.20 and specify the
base field in Definition 2.6.23. The generic field-level normality argument
uses only the actual cover and derived-subgroup predicates and is independent
of valuation theory. The local-field product corollaries meet the corrected
field assumptions. No project errata file for either source was found.

## Implemented proof

`SubgroupFunctor.IsNormal.comap_innerIso` states that comap by an actual
inner automorphism leaves an all-test normal subgroup functor unchanged.
One inclusion is normality; the other applies inverse conjugation and cancels.

`IsDerivedSubgroup.conjugationIso` applies this identity to the represented
scheme-theoretic derived subgroup. The existing `isoOfComap` gives an
automorphism of the actual `D`; its inclusion equation is

```text
conjugationIso(g).hom ≫ d = d ≫ innerIso(g).hom.
```

`IsSimplyConnectedDerivedCover.conjugationLiftIso` lifts that automorphism
to an automorphism of the actual covering group `C` via `isoOver`. Composing
its cover equation with the derived inclusion gives

```text
conjugationLiftIso(g).hom ≫ π ≫ d = (π ≫ d) ≫ innerIso(g).hom.
```

The rational-point version identifies the image of the lifted point with
literal conjugation `g * image(c) * g⁻¹`.
The imported `simplyConnectedImage_normal` from `SimplyConnectedImageNormal`
supplies normality using the existing cover-lifting theorem. The explicit lift
constructed here gives the same rational conjugation formula. Neither argument
assumes that either covering map is surjective on rational points.

For each supplied unramified or base-field zero datum, this normality lets
`Subgroup.mem_sup_of_normal_left` identify the existing join with the product
of its two factors. The membership theorems expand the mapped torus or
centralizer factor to an actual point before multiplication. Finally,
`zeroSubgroupProductMap` multiplies the cover-image point and the mapped
centralizer-zero point. Its surjectivity follows from the membership theorem.

## Remaining obligations

This module reuses normality of the simply connected image; it does not prove normality
or independence of all zero-subgroup data. It does not identify a zero
subgroup with a norm kernel, lift relative root points through the cover,
or prove sharp-fixer boundedness. It preserves the existing definitions and
does not discharge the final centralizer-parahoric intersection target.
