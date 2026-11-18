# Spreading isomorphisms from prime localizations

This internal helper supplies the localization-spreading step needed in the
quasi-finite subscheme exhaustion argument. It treats arbitrary finitely
presented relative schemes, without requiring their total spaces to be affine.

The source and target of the morphism are both finitely presented schemes
over a fixed affine base. Consider a cofiltered system of affine schemes
with compatible maps to that base. If the morphism becomes an isomorphism
over the limit, the proof descends its open-immersion and surjectivity
properties using published relative scheme descent and chooses a common
incoming stage. Conversely, isomorphisms are stable under base change.

Next, the localization at a prime is expressed as the filtered colimit of
principal localizations away from elements outside the prime. The published
`ChartGluing` localization diagram and its colimit witness supply the actual
ring maps. Taking spectra gives the required affine cofiltered limit. The
first theorem and the comparison of the two slice-pullback conventions imply
that an isomorphism after prime localization is an isomorphism after inverting
one element outside that prime. The Prop-valued `Statement` packages this
assertion, and `spreading` proves it.

The provenance is an internal reuse of the Library's limit-descent and
localization-colimit theorems for the localization step of SGA 3, Exposé IX,
Lemma 6.2, printed p.53 (retained PDF p.23), registered as
`sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
No Artinian exhaustion conclusion is proved in this module.
