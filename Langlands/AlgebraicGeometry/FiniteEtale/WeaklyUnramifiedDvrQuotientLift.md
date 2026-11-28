# Finite prime-group quotient values under change of strictly Henselian trait

`WeaklyUnramifiedDvrQuotientLiftStatement` assumes the strict-local Kummer factorization
statement. Let \(W\) be a strictly Henselian DVR with fraction field \(L\). Let \(W'\) be a DVR
with fraction field \(L'\), and let \(W\to W'\) and \(L\to L'\) commute with the fraction-field
maps. Suppose that one uniformizer of \(W\) maps to a uniformizer of \(W'\). For an invertible
prime \(\ell\), a geometric point of \(\operatorname{Spec} L'\) over an algebraically closed
field, and a continuous homomorphism of the induced pointed group over \(L\) to a finite discrete
\(\ell\)-group, every value occurs on restriction to the pointed group over \(L'\).

## Lean proof

Every nonzero DVR element is a unit times a power of the uniformizer. This gives
`isFractionRing_away_uniformizer`, so the spectrum of the ring with the uniformizer inverted
is isomorphic to the spectrum of the fraction field. The uniformizer belongs to the maximal
ideal and lies outside its square, as can be seen by cancellation. These facts allow the
Kummer hypothesis to be applied to the original homomorphism transported along the isomorphism.

The resulting binomial cover is finite étale, and its pointed fundamental group maps into the
kernel of the transported homomorphism. Because the map preserves the uniformizer, the pullback
of this cover over \(L'\) is connected by `uniformizerBinomialPullback`. The conclusion then
follows from `connectedCoverQuotientLift` and functoriality of the pointed maps.

## Source

Deligne, *Résumé des premiers exposés de A. Grothendieck*, SGA 7 I, Exposé I, §0.4.1 and
Variante 1.3, uses the Kummer description of tame inertia and a change of trait preserving
the uniformizer. The Lean result derives the individual finite quotient comparison from the
connectedness of the pulled-back Kummer cover.
