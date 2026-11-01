# Rank-weighted real parts of actual cuspidal tensors

`Langlands.CuspidalTensorRealPartsStatement F T` is an internal adapter
for the supplied compatible topology and residue-normalized absolute value.
The field and representation carrier universes are independent.

For every ordered block shape and actual supercuspidal family `C i`, the
proposition produces real numbers `t i` and scalar characters `c i` of the
original factors. Twisting factor `i` by `|det|^(t i)` is unitarizable.
The original action has scalar character `c i`, with
`‖c i(a)‖ = |a|^(-(B.size i) * t i)`.
Thus the negative sign records that the positive twist is the unitarized
representation, while the scalar character belongs to the original one.

The same characters act on the actual external block tensor through their
coordinatewise product `χ`. Its split-centre real part has coordinates
`-((B.size i : ℝ) * t i)`. These already contain the individual rank weights;
no common factor rank is assumed. Positive ambient rank is unnecessary
for this scalar calculation: every block size is positive by `BlockShape`,
and the empty tensor is included when the shape is empty.

The provenance is internal composition. Real unitarization supplies the
positive twists; the unitary central-character theorem supplies a norm-one
character on each twisted factor. Removing the twist recovers the original
scalar character and its norm. The elementary scalar action on pure tensors
gives the tensor statement. This is a proposed auxiliary proposition, not
a proof, a Jacquet occurrence, a common integral twist line, or a
classification theorem.
