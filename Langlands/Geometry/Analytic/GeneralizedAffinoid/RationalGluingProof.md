# Scalar rational descent for arbitrary positive polyradii

Authors: Worker 101 and Worker 146.

The theorem `RationalChart.wholeSpectrumRationalGluing` has the exact target
`RationalChart.WholeSpectrumRationalGluingStatement.{u, v}`. It concerns the
actual weighted rational quotient algebras and their published product-overlap
restrictions. The field universe `u` and finite cover-index universe `v` remain
independent.

One application of `familyRadiusRealization_nonempty` realizes every base radius
and every chart radius in a complete ultrametric extension field `L : Type u`.
The realization also supplies an isometric coefficient embedding `ι : K →+* L`
and a bounded additive coefficient map `π : L →+ K`, linear along `ι` and
satisfying `π 1 = 1`. The finite family of radii is first enumerated by a finite
ordinal, so an index type in universe `v` does not enlarge the field universe.
Write `Q` for the actual strict scalar extension of the base algebra `A` and
`ψ : BoundedRingHom A Q` for its contractive scalar map.

For each chart `D i`, the realizing tuple `τ i` defines a normalized strict
rational datum `E i` over `Q`: its denominator is the image of the original
denominator, and its numerator in position `j` is multiplied by `(τ i j)⁻¹`.
The constructed contractive map `F i = (D i).normalizedStrictMap ...` takes the
original quotient to the actual strict rational quotient. Its base equation is
`F i ((D i).baseMap a) = (E i).baseMap (ψ a)`. Its fraction equation sends an
original fraction to `τ i j` times the corresponding strict fraction.

`normalizedStrict_cover` pulls spectrum points back along `ψ` and proves that
the `E i` cover the whole spectrum of `Q`. The pairwise
`normalizedStrictMap_compatible` theorem transfers the given equality on each
actual weighted product intersection to equality after the two strict
intersection restrictions. Thus the strict sections `F i (s i)` satisfy the
hypotheses of `wholeSpectrumRationalGluing_finiteIndex`. The actual overlap map
is obtained by extending both realizing tuples with scalar one at their
denominator entry, taking products to realize the original product radii,
and identifying the normalization of the original product datum with the
strict intersection datum. Both restriction squares follow from bounded
ring-map uniqueness over their common contractive base map. This constructs
the compatibility transfer for the published restrictions. This theorem transfers
the published strict gluing result through a finite-ordinal reindexing and
produces a unique `b : Q` with restrictions `F i (s i)`.

The private lemma `scalarDescent_of_compatibleMaps` implements the remaining
algebraic argument. Let `R : Q →+ A` be the actual base coefficient retraction,
and let `R i : (E i).algebra →+ (D i).algebra` be the constructed chart
retraction. These are additive maps; multiplicativity of `π` is neither
required nor asserted. The proved retraction square and left inverse give

```text
(D i).baseMap (R b) = R i ((E i).baseMap b)
                     = R i (F i (s i)) = s i.
```

The first equality is `scalarRetraction_baseMap`. The last is
`scalarRetraction_map`, applied with the proved base equation of `F i`.
The chart retraction is constructed by comparing the normalized strict quotient
with the raw strict scalar extension of the original chart quotient and then
applying its coefficient retraction. The comparison-composite identity follows
from bounded ring-map uniqueness over the common contractive base map.
Consequently no chart sheaf property or gluing operator enters this step.

If `a : A` has the prescribed original restrictions, the base equations of the
`F i` show that `ψ a` has the same strict restrictions as `b`. Strict uniqueness
gives `ψ a = b`, and applying `R` gives `a = R b` because `R (ψ a) = a`.
This proves uniqueness as an equality of actual algebra elements, retaining
nilpotent information.

The construction uses positivity of the radii to invert the realizing scalars.
It adds no nontrivial-valuation, proper-ideal, reducedness, nonempty-spectrum,
positive-arity, or nonempty-cover assumption. Empty coordinate tuples and
rational loci are allowed. In particular, an empty finite cover is handled by
the same strict gluing theorem and the same retraction argument; no index is
chosen from the cover.

The target's source is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p. 9,
and the scalar degree-zero specialization of Fact 2.2.6(i), p. 10. The
implemented proof uses the published strict theorem and the internal scalar
extension, normalization, quotient-map and retraction constructions described
above. It proves scalar existence and uniqueness only; higher Cech exactness,
Banach-module admissibility and categorical sheaf conversion are outside its
conclusion.
