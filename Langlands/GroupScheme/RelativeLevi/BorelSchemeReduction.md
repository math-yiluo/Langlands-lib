# Borel representability from parabolic representability and the clopen locus

Workers 633 and 285.

`relativeBorelScheme_of_parabolicScheme_and_borelLocus` proves the unchanged
`RelativeBorelSchemeStatement` assuming the exact Library propositions
`RelativeParabolicSchemeStatement` and `RelativeBorelLocusClopenStatement`, in
every universe `u`. Both premises remain explicit; this module does not prove
either of them or assert the final unconditional Borel-scheme theorem.

The construction follows Conrad, *Reductive group schemes* (2014), proof of
Theorem 5.2.11(3), p.158. The parabolic-scheme premise supplies an actual smooth
proper parameter scheme `M`, a universal relative parabolic inclusion `j`, and
its unique classification of all relative parabolics. The proof applies
`RelativeLevi.borelSchemeDataOfParabolic` to these data, installs the supplied
smoothness and properness proofs, and unpacks the resulting actual Borel
parameter, source, inclusion and proved properties into the unchanged target.
The supporting `BorelRepresentation` Markdown explains the open restriction,
classification and geometry arguments implemented by that constructor.

`relativeBorelScheme_of_parabolicScheme` then discharges the clopen-locus
premise with the published unconditional theorem `relativeBorelLocusClopen`.
Its sole remaining premise is exactly `RelativeParabolicSchemeStatement`,
with no change to either published statement. This is a conditional reduction;
it does not prove parabolic representability or the unconditional Borel-scheme
target. Both reductions apply to every universe `u` and every base scheme
covered by the published propositions.
