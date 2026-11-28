# Finite étale descent from images of rational domains

`finiteEtaleAffinoidHomDescent_of_rationalImages` proves
`FiniteEtaleAffinoidHomDescentStatement` assuming image recognition for a
single rational chart. The image in question is the image of the locus of
`D : RationalChart K B` under `BanachSpectrum.comap f.toBoundedRingHom`,
transported by `SmallAffinoidSpectrum.spectrumHomeomorph A`. The premise
asks for `IsOriginalChartDomain` in the saturated atlas of `M(A)` for
finite Banach, algebraically finite étale `f : BoundedAlgHom K A B`.

`isOriginalChartDomain_image_chart_of_rational` takes the ambient affinoid
domain of a source chart and uses `Domain.finiteRationalCoverData` to
express it as a finite union of ambient rational loci. The individual images
are closed by compactness of the rational loci and Hausdorffness of `M(A)`.
The finite union is an original chart domain by induction using
`IsOriginalChartDomain.union_of_isClosed`.

`locallyRefines_goodBaseChart_of_chart_images` pulls back the target chart
quasinet along `g` and refines it by source charts using
`isOriginalChartDomain_preimage`. The image of this source quasinet is a
quasinet on `M(A)` because `M(f)` is open and surjective. Within each image
domain the base chart family gives a local refinement. If such a base chart
lies in the image of a source chart mapping into a target chart, every point
over the base chart maps into that same target chart. This follows from
fibre constancy of `g` via `map_eq_of_baseMap_eq`. The resulting base charts
give the refinement used by `exists_hom_of_finiteEtale_of_locallyRefines`.

The covering step follows the chartwise descent argument of Daylies,
Proposition 3.19 and Lemma 3.20. Daylies covers the images of inverse images
of target charts by affinoid domains and descends on their base changes.
Here each inverse image is first refined by source charts, and image
recognition is needed only on their ambient rational pieces. The image
premise is a single-domain case of Ducros's Theorem 9.2.1, applied to the
composite of a rational domain inclusion and a finite étale morphism.
[Daylies, arXiv:2103.10490v3, pp. 21–22](https://arxiv.org/pdf/2103.10490v3#page=21)
[Ducros, *Families of Berkovich spaces*, pp. 184–185](https://arxiv.org/pdf/1107.4259v6#page=194)
