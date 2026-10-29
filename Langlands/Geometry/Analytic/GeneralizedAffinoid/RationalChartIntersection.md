# Explicit common refinements and topological pullbacks of rational charts

Author: Worker 56. The namespace is
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`. This module
packages the published all-products rational quotient as a chosen common
refinement and constructs the universal cone of its actual spectra in
`TopCat`.

## Objects and actual restriction maps

Fix an ultrametric normed field `K`, an actual
`A : PresentedAffinoidAlgebra K`, and two `RationalChart K A` objects `d,e`.
Each chart retains its finite positive polyradius, coefficient-series
representatives and a proof that the denominator and numerators generate
the unit ideal of `A`. Write their data as

\[
 d=(s,g,f_0,\ldots,f_{m-1}),\qquad
 e=(t,h,k_0,\ldots,k_{n-1}).
\]

The definition `inter d e` reuses the all-products presentation from
`RationalPresentation.RationalIntersection`. Extend the coefficient and radius
tuples by

\[
 F=(g,f_0,\ldots,f_{m-1}),\quad H=(h,k_0,\ldots,k_{n-1}),\qquad
 S=(1,s_0,\ldots,s_{m-1}),\quad T=(1,t_0,\ldots,t_{n-1}).
\]

The new chart has arity `(m + 1) * (n + 1)`, denominator `g * h`, numerator
`F a * H b` and radius `S a * T b` at each encoded pair `(a,b)`. The encoding,
positive radii and the proof of unit-ideal generation are the published
`numerators`, `productRadii` and `generatesUnitIdeal`. In particular, this
construction retains the mixed numerator products and the product of the two
denominators.

Its algebra is the existing closed weighted quotient obtained by adjoining
these product coordinates and imposing the old relations and

\[
               ghZ_{ab}-F_aH_b=0.
\]

All coefficients in this equation are understood through the actual
presentation and structural maps. The quotient norm, coordinates and structural
homomorphism are the previously constructed ones. The theorem `locus_inter`
is exactly the published calculation

\[
                 (d.\mathrm{inter}\ e).\mathrm{locus}
                     =d.\mathrm{locus}\cap e.\mathrm{locus}.
\]

The object and this locus equality require no completeness of `K`.

Assume now `[CompleteSpace K]`. The arrows `interLeft d e : d.inter e ⟶ d`
and `interRight d e : d.inter e ⟶ e` use the actual bounded homomorphisms
`RationalIntersection.leftMap` and `rightMap` in the reverse algebra direction.
Their stored structural-map equations are the published
`leftMap_comp_baseMap` and `rightMap_comp_baseMap`. Thus they are morphisms in
the already constructed rational-chart category, with actual bounded
restrictions over `A`. The theorems `norm_interLeft_le` and
`norm_interRight_le` retain the contractive estimates

\[
 \|\rho_d(a)\|\leq\|a\|,\qquad \|\rho_e(b)\|\leq\|b\|,
\]

where `rho_d` and `rho_e` denote the corresponding restriction homomorphisms
into the common-refinement quotient. Completeness enters through the imported convergent relative
evaluation used to construct these restrictions. `inter_spectrum_condition`
then proves that the two induced seminorm pullbacks have equal images in
`BanachSpectrum A`, by applying their respective `spectrumMap_over_base`
equations.

## Continuous lifting and the universal cone

The definition `spectrumInterLift` itself requires no completeness of `K`.
For an arbitrary topological space `X` and continuous maps

\[
 p:X\longrightarrow M(B_d),\qquad q:X\longrightarrow M(B_e)
\]

whose structural images agree pointwise in `M(A)`, it constructs a continuous
map to `M(B_{d.inter e})`. The common base point lies in both loci by the two
published `locusHomeomorph` maps. The proof `hmem` uses `locus_inter` to regard
it as a point of the intersection chart's locus. The lift applies
`(d.inter e).locusHomeomorph.symm` to that subtype point. Continuity follows
from continuity of the base spectrum map composed with `p`, the subtype
construction and the inverse homeomorphism. This construction uses actual
bounded-multiplicative-seminorm spectra and their proved homeomorphisms.

`spectrumMap_spectrumInterLift` records the base image of this lift, using
`locusHomeomorph.apply_symm_apply` and subtype projection. Over complete `K`,
`interLeft_spectrumInterLift` and `interRight_spectrumInterLift` prove its two
projection equations. Each applies injectivity of the original chart's
`locusHomeomorph`, reduces to equality in `M(A)` and uses the structural-map
equations. The right projection also uses the given compatibility of `p,q`.

`spectrumInterLift_unique` proves uniqueness among continuous maps whose first
projection is `p`. The intersection chart's homeomorphism is injective, so
equality reduces to the base images; the first restriction's structural
equation and the prescribed first projection establish that equality. Thus
the second projection need not be an extra hypothesis in this uniqueness
lemma.

`spectrumInterCone` is the `PullbackCone` over the actual structural maps
`TopCat.ofHom d.spectrumMap` and `TopCat.ofHom e.spectrumMap`. Its vertex is
`TopCat.of (BanachSpectrum (d.inter e).algebra)`, its legs are the spectrum
maps of the two constructed restrictions, and its commutativity is
`inter_spectrum_condition`. Finally, `spectrumInterConeIsLimit` constructs
`IsLimit (spectrumInterCone d e)` using `PullbackCone.IsLimit.mk`. For any
competing cone it uses `spectrumInterLift` on the two legs and obtains their
pointwise compatibility from the cone equation. The two projection lemmas
prove factorization, and `spectrumInterLift_unique` proves uniqueness. This
is the categorical pullback universal property in topological spaces over
the base spectrum.

## Provenance and scope

The source context is Vladimir Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Exercise 2.2.2(ii),(iii), printed/PDF page 9, supplies the rational-quotient
and intersection context, and Fact 2.2.3(i), page 10, the spectrum/image
identification context. These pages were read directly. The common denominator
`g` is used throughout the rational inequalities, as in the quotient relation;
the displayed `g_i` in the exercise's inequality is interpreted accordingly.

The chosen common-refinement chart, the continuous lift and the categorical
universal cone are internal derivations from the published concrete quotient,
its restrictions and its spectrum/locus homeomorphisms. They are not claims
that this exact categorical presentation occurs in the original text. The
unit-ideal generation hypotheses remain explicit. The lack of a completeness
hypothesis for the chart and topological lift is a preliminary extension
beyond the original complete-field context; the restriction arrows and the
universal cone are stated over complete `K`.

The result concerns a pullback in `TopCat`. A bounded-algebra pushout universal
property, a product in the rational-chart category and the full affinoid-domain
factorization of Definition 2.2.1 remain separate obligations. It supplies no
structure-sheaf gluing, analytic atlas, etale site or equivariant site. All
quotients use the chosen scalar presentations. Arity zero, arbitrary positive
real radii, trivially valued fields, zero quotients and empty spectra remain
allowed.
