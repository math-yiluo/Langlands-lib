# Filtration when the left induction block has weight zero

This is an internal consequence of the concrete character-induced filtration
proof, induction in stages, and the zero-weight fusion theorem. It formalizes
no additional claim from the literature.

`RealInducedPairLeftZeroFiltrationStatement` quantifies every ambient rank `n`,
surrounding lists `pre`, `post`, and complex character data `d`, `e`. It assumes
`d.weight = 0`, the total-rank equality
`realRank (pre ++ .induced d :: .induced e :: post) = n`, and the strict
inequality
`realBlockExponent (.induced d) < realBlockExponent (.induced e)`. Its conclusion
is the actual
`RealAdjacentFiltration n pre post (.induced d) (.induced e)`.
There is no restriction on the second weight, linking, parity, or exponent gap.

`RealInducedPairLeftZero.filtration` first obtains the closed
`RealCharacterInducedFiltrationStatement` by applying the case assembly
`RealCharacterInducedFiltration.realCharacterInducedFiltration_of`.
The induced-first landing input is `RealSwapLandingIntegral.inducedFirst`;
the character-first input follows by
`RealSwapLandingMirror.characterFirst_of_inducedFirst`; and the uncertainty
input is
`RealOrthogonalUncertainty.realOrthogonalBlockUncertainty`.
Every input to this assembly is thus a proved theorem.

The proof then instantiates
`RealInducedInducedNonzeroReduction.left_zero`. This expands the block of
weight zero into `sgn |·|^t` and `|·|^t`, puts the two character-induced
filtrations into the given ambient module by induction in stages, and fuses
them with `RealInducedPairWeightZero.fuse_left`. Both expanded characters
have the original exponent, so the given strict inequality supplies both
character-step inequalities. Fusion preserves the allowed pieces,
intertwining modulo the earlier ranges, and the spanning conclusion.
The theorem `realInducedPairLeftZeroFiltration` has exactly the named
proposition as its type.

The case-assembly pair `RealCharacterInducedFiltration` is reused unchanged
from Worker 763 and Worker 764's character-induced proof development.
Its paired explanation records the complete case split and its two input
statements; the present module discharges those inputs with the theorems above.
This contribution proves all cases with a zero left weight, including linked
ones. It does not prove the unrestricted two-induced-block target: a nonzero
left weight remains outside its conclusion.
