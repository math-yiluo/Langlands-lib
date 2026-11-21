# From one projected cuspidal block realization to every place constituent

`HasProjectedCuspidalBlockRealization` supplies a single ordered tuple
of actual cuspidal realizations. It supplies a finite induced subquotient
for this tuple and a common surjective linear map to the automorphic
quotient. At each infinite place the source of that map carries the
place operators and normalized block coefficient evaluations.

The lemma `cuspidalSupportEveryPlace_of_projectedCuspidalBlocks` uses the
finite comparison to choose the spectral presentations in the
form-space universe. It uses the supplied real parameter existence
and the proved complex parameter existence at the infinite places.
Separating cuspidal probes embed the source into the ordered standard
module tensored with a multiplicity space. The linear quotient
transports through this embedding to its stable range. The target
irreducible image comes from the nonzero standard tensor extraction
in `CuspidalSupportPlaceTensorAdmissibility`.

The resulting implication has conclusion
`CuspidalSupportEveryPlaceStatement` at universe `u`. The proof uses
the same supplied cuspidal blocks throughout. The supplied common
realization is the global step of Langlands (1979), Proposition 2
and Lemmas 5–6, pp. 204–205 (registered PDF pp. 199–200).
The proof from that step uses the local constituent argument in
Lemma 1, p. 203 (registered PDF p. 198), as in Getz–Hahn (2024),
Theorem 10.7.1 and the following remark, pp. 286–287
(registered PDF pp. 298–299).

The tensor adapters name their local additive group instances explicitly
so their imports can be combined with the cuspidal place isotypy
calculation. The assembly reuses the range transport from
`CuspidalSupportCompactJacquet`.
