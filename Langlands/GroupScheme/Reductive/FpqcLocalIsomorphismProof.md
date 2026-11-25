# Fpqc-locally isomorphic reductive groups are étale-locally isomorphic

`Langlands.GroupScheme.reductiveFpqcLocalIsomorphism` proves exactly
`ReductiveFpqcLocalIsomorphismStatement.{u}` for every universe `u`.
For any scheme `S` and reductive group schemes `G G'` over `S`, an fpqc
cover on whose members the two pullbacks are isomorphic therefore yields
an étale cover on whose members they are isomorphic. The base can be empty.
There are no additional hypotheses or compatibility requirements on the
component isomorphisms.

The implemented proof applies the published
`reductiveFpqcLocalIsomorphism_of_affineSplit` to the published
`affineSplitIsomorphismTheorem`, both at universe `u`. The former has type
`AffineSplitIsomorphismTheoremStatement.{u} →
ReductiveFpqcLocalIsomorphismStatement.{u}`; the latter proves its premise
without any additional assumptions.

The reduction obtains affine étale neighbourhoods on which both groups
have full split coordinates. A field-valued point over the original cover
gives a fibre isomorphism, which identifies their full root data. The affine
split theorem then gives an isomorphism on each neighbourhood, and the
point-indexed family of these neighbourhoods gives the required étale cover.
The details are in
[`FpqcLocalIsomorphismReduction`](FpqcLocalIsomorphismReduction.md);
the affine input is proved in
[`AffineSplitIsomorphismTheoremProof`](AffineSplitIsomorphismTheoremProof.md).

This is an internal composition of published Library results. It imports the
unchanged target, whose source correspondence with Conrad's Proposition
6.2.11(1) is documented in
[`FpqcLocalIsomorphismStatement`](FpqcLocalIsomorphismStatement.md).
