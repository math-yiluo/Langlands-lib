# The Jacquet quotient on one compact compression image

This module constructs `Langlands.Jacquet.compressedImageJacquetMap` and
`compressedImageLift`. The group universe `uG` and representation-carrier
universe `uV` are independent. The group is any topological group; the
representation is a smooth complex representation, `K` is a compact open
subgroup, and the actual subgroup `M` normalizes the actual subgroup `N`.
There is no finite-dimensionality, admissibility, local-field or reductivity
restriction.

The source motivation is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VI.6.1, printed p.177 / PDF p.183,
from (VI.6.1.2) through the section and following Proposition. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The author read that passage in the 2026 edition. These are derived
constructions that isolate its restricted quotient and inverse. Their
elementary laws use the inverse of an actual linear bijection.

## Carriers and maps

Write `W = fixedVectors ρ K.toSubgroup` and
`Q = fixedVectors (Jacquet.action ρ N M hMN) (K.toSubgroup.comap M.subtype)`.
Both are the existing submodules, and `j : W →ₗ[ℂ] Q` is exactly
`fixedJacquetMap`. Its value is the actual coinvariant class of the input.
For any `g : G`, the operator `C_g = compressedAction ρ hρ K hK g` is the
existing normalized compact average of `ρ(g)v` on `W`. Thus on `K`-fixed
vectors it is Renard's `π(a_{g,K})`.

`compressedImageJacquetMap` is `j` composed with the subtype inclusion
`range C_g →ₗ[ℂ] W`. Its domain is the image of this single operator.
The application lemma is definitional.

`compressedImageLift` takes a proof `hb` that precisely this restricted
quotient is bijective. It is the inverse of
`LinearEquiv.ofBijective (compressedImageJacquetMap ...) hb`, followed by
the inclusion into `W`. The parameter `hb` is required to define this inverse;
the module does not provide such a proof from contraction hypotheses.

## Intrinsic laws

All the following declarations are in `Langlands.Jacquet`.

| Declaration | Conclusion |
| --- | --- |
| `fixedJacquetMap_compressedImageLift` | Applying `j` to the lift gives the original quotient vector. |
| `compressedImageLift_mem_range` | Every lifted vector belongs to `range C_g`. |
| `compressedImageLift_unique` | A vector in `range C_g` with quotient class `y` equals the lift of `y`. |
| `range_compressedImageLift` | The lift's range is exactly `range C_g`. |
| `compressedImageLift_eq_of_range_eq` | If two compression images are equal and both restricted quotients are bijective, the two lifts are equal as linear maps into the same `W`. |

The right-inverse law and membership are the inverse identities and subtype
property. Uniqueness applies the inverse to the given quotient equality.
For the range equality, one inclusion is membership; for the other, a vector
in `range C_g` is the unique lift of its own quotient class. The final equality
uses that same uniqueness, transporting image membership along the given
submodule equality. It proves no equality of compression images.

## Remaining source obligations

Renard first proves that every sufficiently contracting element annihilates
the entire fixed-vector quotient kernel, uniformly over an epsilon chamber.
He then proves bijectivity on the single image, its complementarity to the
quotient kernel, and independence of the resulting image and section from
the chosen element. Those are separate statement and proof obligations.
No one of them is a structural hypothesis or conclusion of this module.

In particular the hypotheses `hb`, `hb'` and the range equality in the last
intrinsic lemma are not claims that those properties follow from arbitrary
`g` and `g'`. The module does not assert that a choice of inverse alone proves
the source's independence Proposition. The general reductive specialization
must use the shared actual standard parabolics, split component, character
chambers and rational-point topology, with the Chapter V structural inputs
visible. Comparison with the existing intersection of all power images
`stableImage` is also separate.
