# Weighted rational and Weierstrass quotient presentations

Worker 56 constructed this module, adapting the rational equations,
unit-ideal predicate and coordinate argument from Worker 36's published
`RationalPresentation/Definitions`, and the forward-spectrum argument from
`WeierstrassPresentation`. Worker 36 is a coauthor of this adaptation.

## Inputs and the actual quotient

Work over an ultrametric normed field `K`. Fix an actual
`PresentedAffinoidAlgebra K` named `A`, with arity `n`, positive polyradius
`r = A.polyradius`, closed ideal `I = A.ideal`, quotient carrier
`K{r⁻¹T}/I`, and quotient map `q_A = presentationMap K A`. Choose a
strictly positive real polyradius `s` on `Fin m` and explicit old-series
representatives `g` and `f j`. Put `ḡ = q_A(g)` and `f̄_j = q_A(f j)`.
All declarations below belong to
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation`.

`GeneratesUnitIdeal` is the proposition

\[
  \langle\bar g,\bar f_1,\ldots,\bar f_m\rangle=A.
\]

It is expressed as equality of the actual ideal span with `⊤` in `A`.
This predicate is recorded for subsequent localization results; none of
this module's constructions or theorems assumes it. In particular, the
module does not prove an equivalence between this predicate and the absence
of common spectral zeros.

Write `i = GeneralizedTateAlgebra.appendLeft r s K` for the existing
old-variable inclusion. `equations` is the range of the actual series
`i(g) * Y_j - i(f j)`. Applying the published `Adjoin.algebra` gives
`algebra`, the concrete normed quotient

\[
  B=K\{r^{-1}T,s^{-1}Y\}/
    \overline{\langle i(I)\cup\{i(g)Y_j-i(f_j):j\in\operatorname{Fin}m\}\rangle}.
\]

The included old relation set contains every element of `I`. The new
variables are indexed by `Fin.natAdd n j`, while the old variables are
indexed by `Fin.castAdd m i`. The quotient carries the inherited quotient
norm; no abstract algebra satisfying an assumed localization property is
supplied as input.

No coefficient completeness, nontrivial valuation, value-group condition,
proper-ideal condition or reducedness assumption is used. Both finite
arities may be zero, and the quotient may be the zero ring. If `K` is
complete, the imported completeness instances for presented affinoid
algebras apply to `A` and `B`. Without that hypothesis these are still the
explicit normed algebras constructed by the imported definitions.

## Structural map and fraction coordinates

`baseMap` is the bounded `K`-algebra homomorphism `A → B` supplied by
`Adjoin.baseMap`. The representative identity
`baseMap_presentationMap` is definitional:

\[
  \operatorname{baseMap}(q_A(h))=q_B(i(h)).
\]

`norm_baseMap_le` reuses the adjunction contraction
`‖baseMap(a)‖ ≤ ‖a‖`. `baseMap_coordinate` reuses the identity taking an
old quotient coordinate to the corresponding first-block coordinate of `B`.
These facts follow from the previously constructed descent of the
old-variable inclusion through the old quotient ideal.

`fraction j` is the actual new quotient coordinate. Its bound
`norm_fraction_le` is `‖fraction j‖ ≤ s j`, by the adjunction coordinate
bound for the appended polyradius. `fraction_equation` proves

\[
  \operatorname{baseMap}(\bar g)\operatorname{fraction}_j
    =\operatorname{baseMap}(\bar f_j).
\]

Its proof applies `Adjoin.presentationMap_equation` to the corresponding
member of `equations`, exposes the quotient ring map, and rewrites its
preservation of subtraction and multiplication. The name `fraction` refers
to this equation: invertibility of the denominator is not asserted here.

## Closed locus and forward spectrum map

`locus` is the following subset of the concrete multiplicative spectrum:

\[
  V=\{x\in\operatorname{BanachSpectrum}(A):
          x(\bar f_j)\le s_j x(\bar g)\text{ for every }j\}.
\]

`isClosed_locus` writes it as an intersection of closed inequalities between
continuous evaluation functions, using continuity of multiplication by
`s j`. `isCompact_locus` applies closed-subset compactness to the imported
compact spectrum. Those spectrum constructions and compactness results
hold for normed commutative rings and do not require completeness here.

`spectrumMap` is the continuous map from `BanachSpectrum B` to
`BanachSpectrum A` constructed by precomposition with `baseMap`.
`spectrumMap_mem_locus` proves its forward image lies in `V`. For a point
`x` of `B`, the fraction equation and multiplicativity give

\[
  x(\operatorname{baseMap}(\bar f_j))
   =x(\operatorname{baseMap}(\bar g))x(\operatorname{fraction}_j)
   \le x(\operatorname{baseMap}(\bar g))s_j.
\]

The inequality uses the point's domination by the quotient norm,
`norm_fraction_le`, and nonnegativity of the denominator's seminorm. There
is no division and no hypothesis that the denominator evaluates nonzero.

## Denominator-one specialization

`weierstrassAlgebra` and `weierstrassMap` abbreviate `algebra` and `baseMap`
with series denominator `1`. `weierstrass_fraction` simplifies the fraction
equation using preservation of one, identifying each new coordinate with
the image of `f̄_j`. `weierstrassLocus` is the set defined by
`x(f̄_j) ≤ s j` for every `j`. `locus_one` identifies it with the rational
locus for denominator one by the spectrum point's value at one.
`spectrumMap_mem_weierstrassLocus` then rewrites the proved forward
containment along that equality. Empty tuples give vacuous locus conditions;
the construction and proofs impose no nonempty-tuple assumption.

## Provenance and scope

The original source context is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009): Example 1.2.2(v) and Definitions
1.2.3, 1.2.5, printed/PDF page 4; the quotient norm discussion and
Definitions 2.1.1–2.1.2, page 7; and Exercise 2.2.2(i)–(ii), page 9.
The registered source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

The source's rational construction uses a common denominator, positive
radii, and no common zeros; its displayed relations are `gT_j-f_j`.
Its Weierstrass construction uses `T_j-f_j`. These supply the equations and
loci specialized here to an explicit old presentation. The implemented
construction is derived: it forms a closed quotient directly over `K`,
reuses the actual adjunction maps, and proves the intrinsic relations,
norm bounds and forward spectral inequalities. These arguments justify
omitting coefficient completeness and the no-common-zero condition for
this limited conclusion; the source's analytic-domain theorem is stated
in the complete-field setting and is not being extended here.

The inputs retain explicit representatives in the old series algebra.
Independence from representatives or presentations, comparison with
relative series over `A`, denominator invertibility under the unit-ideal
condition, bounded localization extension, reverse spectrum inclusion and
analytic-domain representability remain separate obligations. This module
constructs the presentation needed to formulate those results.
