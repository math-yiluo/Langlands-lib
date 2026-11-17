# Lifting through the last three incoming crossings

This internal construction studies the full-character part of the linked
incoming map. The two middle multipliers do not vanish on their parity
classes. Their pointwise inverses define reverse Frobenius maps, giving an
explicit equivalence of the full-character spaces before and after the two
middle crossings. Consequently the middle crossings do not enlarge the
kernel of the first crossing.

The final crossing is the outer binomial. Its pointwise inverse is a right
inverse on vectors supported in the central low modes. Composing this inverse
with the reverse middle crossings gives a linear `lift`. The last three
incoming crossings, denoted `suffix`, send this lift back to the original
vector whenever its high central modes vanish. Conversely every suffix output
has vanishing high central modes. Thus the suffix range on its full-character
domain equals the full central-tail kernel.

In particular every vector in the actual outer-tail kernel, retaining both
original induction conditions, has the displayed lift through the suffix.
This conclusion places the lift only in the full-character space. Membership
in the range of the first crossing on the actual incoming two-induced-block
source is a separate, unproved condition. No equality of the actual incoming
range with the restricted outer-tail kernel, nonzero actual incoming map,
inner-window image theorem, or full adjacent filtration is asserted.

The proofs use the published block Fourier multiplier formula, the
nonvanishing support criterion for binomial multipliers, and Fourier
coefficient detection on the compact group. The lift uses inverse binomial
multipliers and is not claimed to intertwine real Lie derivatives.

`RealInducedPairIncomingLiftStatement` packages these conclusions for every
linked pair at the explicit canonical resonance parity. The multipliers and
`MultiplierData` exist by `RealInducedPairLinkedIncoming.exists_multiplierData`;
the first signed multiplier and final binomial are fixed as in that module.
The packaged conclusions retain nonvanishing of both middle multipliers,
equality of the first and third crossing kernels on the actual incoming
source, the full-character suffix range equality, and the displayed lift
identity on the actual outer-tail kernel. The accompanying theorem proves
this proposition from the constructions above. The middle equivalence and
lift are complex linear maps; no Lie intertwining is asserted for the inverse
binomial.
