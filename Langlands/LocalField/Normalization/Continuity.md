# Continuity of the normalized absolute value

`Langlands.PadicField.TopologicalData.continuous_normalizedAbs` states that,
for every prime `p`, every `F : PadicField.{u} p` and supplied
`T : F.TopologicalData`, the real-valued function `T.normalizedAbs` is
continuous for `T.topology`. The field universe remains arbitrary.

The proof rewrites the supplied topology as the canonical norm topology,
then uses the published identity
`T.normalizedAbs x = ‖x‖ ^ Module.finrank (Padic p) F.Carrier`.
Continuity follows from continuity of the norm and of natural powers.

The existing private
`continuous_normalizedAbs` helper was moved from
`Langlands.Representation.RankinSelberg.RootFiniteFunctionProof` into this
module, preserving its proof and making the field argument implicit.
The same continuity statement had been proved independently in
`Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof`.
That duplicate was removed, and both modules now import this shared
declaration under the public name used in `SchwartzBruhatValuationBoundsProof`.
This extraction changes
neither continuity statement nor either consuming theorem.
