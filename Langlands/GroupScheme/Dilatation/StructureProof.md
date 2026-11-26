# Smoothness and geometric connectedness of dilatations and congruence models

`Langlands.GroupScheme.IntegralModel.dilatationStructure` proves
`Langlands.GroupScheme.IntegralModel.DilatationStructureStatement`. The dilatation
of a smooth affine DVR model along a smooth closed subgroup of the residue fibre
is smooth. Its special fibre is geometrically connected when the centre is
geometrically connected. If the supplied generic group is also geometrically
connected, all its fibres are geometrically connected. Every positive congruence
model of a smooth model is smooth with geometrically connected special fibre.
All its fibres are geometrically connected when the supplied generic group is
geometrically connected.

The proof compares the actual schemes with their relative affine coordinates.
The coordinate ring of the centre is the quotient by the kernel of the
coordinate map of its closed immersion into the original model. The uniformizer
lies in this kernel because the centre is over the residue field. The special
fibres of the original model and the dilatation are spectra of their coordinate
rings modulo the uniformizer. For the morphism from the dilatation's special
fibre to the centre, the proof checks the identity over the residue field by
cancelling the closed immersion of the residue point into the base.

Smoothness over the residue field gives regularity of the original special-fibre
and centre coordinate rings. The polynomial descriptions at the local rings of
the centre give flatness and polynomial fibres after any field base change.
`ResidueGeometry` uses these descriptions to prove that the special-fibre
projection is smooth with geometrically connected fibres. `StructureReduction`
combines this with the supplied generic identification and uses
`positiveCongruenceModelAddIso` to pass to all positive levels.

## Source

The proof follows the chart of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Appendix A.5.9–10, and the congruence iteration in A.5.12–14,
printed pp. 635–637 (PDF pp. 666–668). The regular-equation calculation and
the fibre criteria apply over a general discrete valuation ring.
Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
