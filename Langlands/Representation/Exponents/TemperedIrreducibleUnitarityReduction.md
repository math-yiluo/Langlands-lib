# A conditional form construction for the VII.2.6 corollary

Author: Worker 346. This is internal assembly of the published discrete-series
embedding statement and positive-form constructions. It retains its inputs and
does not prove the unconditional VII.2.6 corollary.

`temperedIrreducibleUnimodularForm` takes the exact
`TemperedIrreducibleDiscreteSeriesStatement` as a premise. For the original
irreducible normalized-exponent tempered representation, it chooses an actual
parabolic, Levi, radical and square-integrable representation with the embedding
supplied by that statement. It builds the square-integrable representation's
form using `rationalSquareIntegrableUnimodularForm`, induces that form using
`leviInductionUnimodularForm`, and restricts it along the supplied injective
intertwiner with `InvariantPositiveForm.comap`.

The field universe `u` and carrier universe `v` are independent. The chosen
representation of the Levi uses its canonical `leviPointTopology`; its local
compactness and nonarchimedean group structure come from the published Levi-point
transport. The ambient and Levi Hausdorff instances come from their canonical
rational-point topologies. The original square-integrability premise still
quantifies over every Borel Haar measure on the quotient by the full center.
The chosen induced carrier has universe `max u v`, while the output form is
on the original carrier of universe `v`.

The retained geometric inputs are
`RationalReductiveUnimodularityStatement`, its explicit
`StandardCocharacterStatement` premise,
`ArbitraryParabolicQuotientCompactStatement`, and the displayed modular-character
identity for every actual parabolic/Levi/radical datum in the given ambient group.
The first input supplies both ambient and Levi unimodularity. The compactness
input supplies the actual left quotient for the chosen parabolic. No claim is
made that these inputs have been proved, nor that this conditional constructor
is a proof of `TemperedIrreducibleUnitarizableStatement`.

The construction follows the form-restriction route documented by the
published VII.2.6 statement pair. Its provenance is composition of existing
Library interfaces; it introduces no additional literature assertion.
