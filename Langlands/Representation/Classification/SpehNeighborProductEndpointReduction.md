# The endpoint reduction from binary Langlands-head occurrence

This internal helper proves
`spehNeighborProductEndpointSubquotient_of_headProductSubquotient`: the binary
Langlands-head occurrence proposition implies the exact Speh endpoint target,
with independent field and carrier universes and all supplied actual
representations and rank transports retained. It is a conditional reduction;
the separate entry module supplies the proved occurrence theorem.

The proof extracts a segment whose special head is the discrete-series block,
identifies the three supplied Speh representatives using
`SpehSegmentParameters`, and chooses a head of the sum of the neighboring
parameters. Binary head occurrence and the assumed irreducibility of the
neighbor product give an actual isomorphism from the chosen head to that
product. The centered multiset identity identifies this same sum with the sum
of the two opposite half-twists of the length-k parameter. Real-twist
compatibility identifies the actual twisted copies of the supplied S as the
two heads. Applying binary occurrence again and transporting the earlier
isomorphism gives the desired actual subquotient.

The private equality helpers handle dependent rank transport. In particular,
the binary shape with equal block sizes and the uniform two-block shape
induce the same actual representation after total-rank transport: their ordered
sizes and actual twisted factor families agree. The caller's exact
rank equality transports both the chosen head and neighbor product at the
start of the final comparison. A generic equality-elimination lemma moves the
inverse equal-block-rank transport from the constituent to the ambient
representation, retaining that exact supplied transport on the constituent. The general
irreducible-subquotient rigidity lemma is imported from the Library.

This is derived from the published centered-parameter, real-twist,
essentially-square-integrable classification and head-existence interfaces.
Its source-level argument is Tadić 1986, A.4(ii) and A.6(i), printed pp.372–375
(`tadic-1986-unitary`, PDF pages 39–42), with the centered a(delta,k) notation
before A.8 on p.375. It uses A.4(ii) twice; no separate A.6 assertion or Speh
unitarizability premise is assumed.
