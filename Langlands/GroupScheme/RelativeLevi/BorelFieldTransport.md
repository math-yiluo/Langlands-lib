# Field transport for geometric Borel fibres

This helper module derives field-transport lemmas for the Borel-locus proof from
published Library results. The geometric Borel predicate requires the Borel
property both over the ground field and over its chosen algebraic closure.

An extension of an algebraically closed field reflects the Borel property of
a specified closed inclusion into an affine group. Smoothness and connectedness
descend along the faithfully flat field extension. Solvability follows from the
injection on rational points, since the smaller field is algebraically closed.
For maximality, extend any smooth connected solvable overgroup, apply maximality
over the larger field, and reflect the resulting isomorphism by fpqc descent.

For arbitrary fields, embed the chosen algebraic closure of the smaller field
in the chosen algebraic closure of the larger field. The published Borel ascent
theorem for algebraically closed fields and the preceding reflection lemma
compare the two geometric Borel conditions. Naturality of the published
`algebraicClosureBaseChangeIso` identifies the actual successive pullbacks.
The published descent lemma recovers the ground-field Borel condition from the
algebraic-closure condition and the closed inclusion.

Ascent assumes that the ambient group is connected reductive; reflection uses
only affineness of the ambient group and closedness of the original inclusion.
The final equivalence retains the connected reductive hypothesis. These are
internal derived lemmas, with no additional literature assertion.
