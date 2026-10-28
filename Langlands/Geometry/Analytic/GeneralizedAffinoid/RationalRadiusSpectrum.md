# Closed spectrum embeddings for smaller rational radii

Worker 56 derives this construction from the published weighted rational
spectrum theorem and the actual scalar radius restriction. It identifies
the spectrum map for smaller radii with inclusion of the corresponding
closed inequality subspaces.

All declarations are in
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation`.
The coefficient field `K` is an ultrametric normed field; completeness is
not assumed. `A` is an actual `PresentedAffinoidAlgebra K`, `g` and `f j`
are its scalar series representatives, and `s,t` are positive radii on
the common finite new-variable block. Write

\[
 B_s=\operatorname{algebra}(K,A,s,g,f),\quad
 i_s=\operatorname{baseMap}(K,A,s,g,f),\quad
 Y_{s,j}=\operatorname{fraction}(K,A,s,g,f,j).
\]

These are the existing closed quotients, bounded structural maps and
quotient coordinates. The relation is
`i_s(gbar) * Y_s,j = i_s(fbar_j)`. The actual scalar rational inequality
subspace of `M(A)` is denoted by `V_s`.

## Rational locus homeomorphism

Assume `hunit : GeneratesUnitIdeal K A g f`, the existing condition that
the denominator and numerator classes generate the unit ideal in `A`.
The published `isClosedEmbedding_spectrumMap` and `range_spectrumMap`
give an embedding of `M(B_s)` whose range is exactly `V_s`.
`locusHomeomorph` composes the embedding's homeomorphism onto its range
with the equality of that range and `V_s`. Its forward function is the
existing structural spectrum map, as stated in
`locusHomeomorph_apply_coe`.

`locusHomeomorph_symm_apply` identifies its inverse with the published
`pointLift` of a point of `V_s`, constructed using bounded evaluation
in that point's completed residue field. The proof applies injectivity
of the structural spectrum map and its already proved right inverse.
Thus the homeomorphism packages existing proved constructions.

## Fraction inequalities inside the quotient spectrum

For any two positive polyradii, with no ordering or generation assumption,
`fractionLocus K A s t g f` is the actual subset

\[
 W_{s,t}=\{x\in\mathcal M(B_s)\mid
              x(Y_{s,j})\leq t_j\text{ for every }j\}.
\]

`isClosed_fractionLocus` uses continuity of each spectrum evaluation
and closedness of real inequalities. `isCompact_fractionLocus` uses
compactness of the spectrum. `fractionLocus_self` proves
`W_s,s = M(B_s)` from the published norm bound for each fraction
coordinate and domination of every spectrum point by the norm.

Under `hunit`, `spectrumMap_mem_locus_iff` proves

\[
 i_s^*(x)\in V_t\quad\Longleftrightarrow\quad x\in W_{s,t}.
\]

The structural point lies in `V_s`, so the published denominator
nonvanishing theorem gives `x(i_s(gbar)) > 0`. Applying the multiplicative
seminorm to the fraction equation gives

\[
 x(i_s(\bar f_j))=x(i_s(\bar g))\,x(Y_{s,j}).
\]

Multiplication by this positive denominator value converts each fraction
inequality into its base rational inequality, in both directions.
This equivalence does not need `t <= s`.

## Smaller-radius spectrum image

Now assume `hts : ∀ j, t j ≤ s j`. The published contractive algebra map
`radiusMap : B_s → B_t` induces the actual continuous spectrum pullback
`radiusSpectrumMap : M(B_t) → M(B_s)`.

`radiusSpectrumMap_injective` uses its existing structural square over
`M(A)` and injectivity of the structural map from `M(B_t)`.
`isClosedEmbedding_radiusSpectrumMap` then uses compactness of the
source and Hausdorffness of the target.

`range_radiusSpectrumMap_eq_preimage` proves

\[
 \operatorname{range}(R_{s,t}^*)=(i_s^*)^{-1}(V_t).
\]

The proof uses a private set-theoretic lemma for a composite `q ∘ r = p`
with injective `q` and known range of `p`. Forward containment follows
by mapping a point through that composite. For the reverse direction,
range membership lifts `q(x)` through `p`; the composite identity and
injectivity of `q` identify its image under `r` with `x`. Applying this
lemma to the structural maps, their published square, injectivity at `s`
and the exact range theorem at `t` proves the displayed identity.

Combining this equality with the fraction-inequality equivalence gives
`range_radiusSpectrumMap`:

\[
 \operatorname{range}(R_{s,t}^*)=W_{s,t}.
\]

`radiusSpectrumHomeomorph` is the resulting homeomorphism
`M(B_t) ≃ₜ W_s,t`. Its forward function is the actual spectrum pullback.
`radiusSpectrumMap_radiusSpectrumHomeomorph_symm` records that its inverse
maps back to the prescribed point of the closed fraction subspace.

Finally, `radiusLocusInclusion` is the continuous inclusion `V_t → V_s`,
constructed from the published monotonicity of rational inequalities.
Its underlying function preserves the base spectrum point. It is a
closed embedding by continuity, compactness and injectivity of subtype
inclusion. This construction and its closed-embedding theorem use no
unit-ideal generation. `locusHomeomorph_radiusSpectrumMap` proves that,
under generation, the radius spectrum map becomes this inclusion after
the two structural homeomorphisms. The proof is subtype extensionality
and the published structural square.

## Provenance and scope

The original context is Vladimir Berkovich, *Non-Archimedean analytic
spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Exercise 2.2.2(i)-(ii), printed/PDF page 9, supplies the Weierstrass
inequalities, common-denominator rational equations and positive radii.
Fact 2.2.3(i), printed/PDF page 10, gives the source context for
identification of an affinoid-domain spectrum with its image.

The present homeomorphisms and radius image formula are internal
derivations from the published concrete quotient constructions and
spectrum identification. Their Lean proofs are described above. The
unit-ideal condition is explicit. This module does not prove the full
analytic-domain universal property of Definition 2.2.1 or assert that
the smaller-radius algebra is a newly constructed Weierstrass quotient.
It identifies its spectrum with the stated actual inequality subspace.

Empty variable blocks, arbitrary positive radii, trivially valued fields
and zero quotients are permitted. No algebraic inverse to radius
restriction, injectivity or surjectivity of that algebra map, quotient
norm isometry, structure sheaf, atlas or analytic site is asserted.
