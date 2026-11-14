# The torus character-kernel theorem

`TorusCharacterKernelStatement` is the rational-point form of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Lemma 11.1.3, printed p. 422,
PDF p. 453, together with the restriction paragraph following Proposition
11.1.5, printed p. 423, PDF p. 454. The November 2024 corrections do not
change these assertions.

For every nonarchimedean local field `F` and actual `F`-torus `T`, the statement
equates the existing rational-character valuation kernel with the inverse image
of torsion in the actual geometric cocharacter inertia quotient. The map on
`T(F)` is the composition of the rational/coefficient point equivalence,
extension to `UnramifiedClosure F`, and the constructed `torusKottwitz` map.
Thus the statement is independent of any unproved specification of the separately
selected invariant-valued `torusKottwitzRational`.

The original lemma identifies the character valuation map with the Kottwitz map
followed by the cocharacter-to-invariant-character-dual map, whose kernel is
torsion. The paragraph on the following page states that the resulting kernel
identity remains valid on rational points. The Lean statement records that
kernel identity for the Library's multiplicative valuation convention, where
character values have valuation one. It restricts the source's field scope to
the nonarchimedean local fields used by the present Kottwitz construction.

This is a proposition to prove, not a supplied hypothesis or a proof of the
identity. It is a separate torus prerequisite for the reductive character-kernel
theorem.
