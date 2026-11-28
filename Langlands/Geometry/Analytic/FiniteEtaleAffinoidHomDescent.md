# Descent of analytic morphisms along finite étale affinoid covers

`Langlands.Analytic.SaturatedAtlasPresentation.finiteEtaleAffinoidHomDescent`
proves `FiniteEtaleAffinoidHomDescentStatement.{u, v}`. Let
`f : A → B` be finite Banach, algebraically finite étale and surjective
on Banach spectra. The algebras are presented affinoid algebras over a
complete ultrametric normed field \(K\) in universe `u`, possibly
trivially normed, with `v`-small spectra. For any localized morphism
`g : M(B) ⟶ T` that agrees on all parallel morphisms identified by
`M(f)`, there is a localized morphism `h : M(A) ⟶ T` with
`M(f) ≫ h = g`. The target lies in `LocalizedCategory.{u, v, v}`.

The theorem applies `finiteEtaleAffinoidHomDescent_of_rationalImages`
to `isOriginalChartDomain_image_rational`. For this image lemma the
norm polynomial of the linear form in the rational data detects
whether a fibre contains a point satisfying the rational inequalities.
The weighted coefficient criterion gives a finite union of rational
loci on the base by using each eligible maximal coefficient as a
denominator. The saturation of the base affinoid atlas recognizes the
resulting image as an analytic domain. The finite rational covers of
source charts extend this to images of all source charts.

Choose a saturated representative of the localized target. Pull its
chart quasinet back along \(g\) and refine by source charts. Their
images form a quasinet on the base by openness and surjectivity of
\(\mathcal M(f)\). Refine each image domain by base charts. The
kernel-pair condition implies that \(g\) is constant on the point
fibres of \(\mathcal M(f)\), so the inverse image of each of the
resulting base charts maps into a single target chart.

On every such base chart, the pulled-back cover is finite Banach,
flat and surjective on spectra. The restricted map into the target
chart descends by bounded affinoid descent. An \(A\)-linear retraction
of a finite faithfully flat affinoid map supplies the bound needed to
descend the algebra homomorphism, including over trivially normed
fields. The local maps agree by étale base change and
`etaleCoverHomExt`. The proof glues them by
`exists_hom_of_chartCover` and checks their composite with
\(\mathcal M(f)\) by `localizedHom_ext_of_chartCover` on the source.

Berkovich’s Proposition 4.1.3 gives the chartwise descent argument
for good targets. Remark 4.1.5 identifies the image property used
for arbitrary targets. Conrad–Temkin’s Theorem 4.1.2 establishes
that property for finite étale maps, and Daylies’s Lemma 3.20 uses
image domains for the covering step. The Lean proof obtains the
needed images from the determinant and weighted rational inequalities.
[Berkovich, Proposition 4.1.3 and Remark 4.1.5](https://www.numdam.org/item/PMIHES_1993__78__5_0/)
[Conrad–Temkin, Theorem 4.1.2](https://math.stanford.edu/~conrad/papers/analgpaper.pdf#page=18)
[Daylies, Lemma 3.20](https://arxiv.org/pdf/2103.10490v3#page=22)
