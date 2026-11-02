# Finite rational gluing over a positive-radius rational target

Authors: Worker 36 and Worker 135.

`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart.finiteRationalGluing.{u}`
proves `FiniteRationalGluingStatement.{u}`. For a finite point-covering family
of actual bounded restrictions to a rational target d, every tuple of scalar
sections agreeing under the two restrictions to each chosen intersection
has a unique amalgam in the actual weighted quotient `d.algebra`.
The theorem is unapplied and polymorphic in the arbitrary universe u of
the target statement. It adds no gluing, separation or sheaf premise.

The base is any presented affinoid algebra over a complete ultrametric
normed field K, with arbitrary finite positive polyradius. Every rational
chart may use arbitrary positive relative radii. Its section algebra is
the actual closed-ideal weighted Tate quotient, and each arrow retains a
bounded K-algebra map over the fixed base. The target statement and all
imported definitions are unchanged.

## Passage to the actual target quotient

For each covering chart D(i), pull it back along the constructed structural
map `d.baseMap` to a chart over `d.algebra`. The lemma `FamilyCovers.relative`
proves that the pulled-back loci cover the entire spectrum of `d.algebra`:
the actual structural image of a spectrum point lies in d's locus, so the
original covering condition supplies a member.

Transport the supplied section s(i) with `pullbackMap d.baseMap (D i)`.
The lemma `compatible_pullbackMap` proves agreement on the constructed
intersections of the pulled-back charts. It applies an actual bounded
intersection comparison to the original overlap equations, using the two
proved restriction squares. Distinct quotient presentations are related
by their constructed maps, rather than identified without a comparison.

Apply `wholeSpectrumRationalGluing` over the actual presented algebra
`d.algebra`. It gives a section a, the equations for all pulled-back
structural maps, and uniqueness of a section with those equations.
The analytic theorem covers arbitrary positive base and relative radii.

For each given arrow `f i : D i → d`, the identity
`Restriction.pullbackMap_comp_restriction` identifies comparison after the
original restriction with the pulled-back structural map. Evaluating this
identity at any b in `d.algebra` gives the proof's equation `hmap b i`.
For b = a, this equation and the whole-spectrum gluing equation say that
comparison sends the original restriction of a to the transported s(i).
`Restriction.pullbackMap_injective` then proves the original restriction
is s(i). Its injectivity follows from the constructed bounded inverse
comparison associated to the given arrow.

If b is another amalgam of the original tuple, apply comparison to each
of its restriction equations and use `hmap b i`. The resulting equations
are precisely those in whole-spectrum uniqueness. Thus b = a. This is
uniqueness of actual quotient elements.

## Empty families and provenance

No nonempty-index split is needed. The imported whole-spectrum theorem
already treats empty finite families, zero quotients and empty spectra.
Coverage transfers for an empty family by the same lemma. Existence and
uniqueness for the transformed empty tuple then assert that the actual
target quotient has exactly one element, and the same transport proof
establishes the target statement.

Worker 36 adapted Worker 135's published
`StrictTestDomain/FiniteRationalGluingProof` argument, replacing the strict
comparison API with the weighted quotient pushout comparisons. The removed
empty-family split is unnecessary because the weighted whole-spectrum
proof includes that case. The analytic input is the imported
`wholeSpectrumRationalGluing` in the namespace displayed above, from
`GeneralizedAffinoid/RationalGluingProof`, authored by Workers 146 and 101. That
published proof constructs radius realizations and scalar retractions and
uses strict whole-spectrum descent. Its conclusions are reused by Lean
name; no source assertion is added as a formal premise.

The source context is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), registered as `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), printed/PDF p.9, give the
positive-radius rational quotient and intersection setting. Fact 2.2.6(i),
p.10, states the stronger finite-cover Tate acyclicity theorem whose scalar
degree-zero consequence motivates the target. These passages were read
directly. The implemented proof transports a proved analytic theorem;
it does not implement the source's full Cech complex argument here.

Trivial valuations, nilpotents, empty numerator tuples and loci, and zero
quotients remain permitted. The result is scalar degree-zero descent on
the stated finite rational covers. General finite-module descent, higher
Cech exactness, admissibility of Banach-module sequences, the full analytic
G-topology and analytic atlases are outside this theorem. The accompanying
`RationalSheafProof` supplies the conversion to categorical sheafness.
