# Transport of continuous irreducible classes through isomorphic quotients

Let \(N\) and \(M\) be normal subgroups of the topological groups \(G\)
and \(H\). A continuous group isomorphism \(\phi:G/N\to H/M\) induces
`Langlands.FiniteRepresentation.continuousIrreducibleQuotientTransport`.
It is a bijection between the rank-\(n\) continuous irreducible complex
classes of \(G\) trivial on \(N\) and the rank-\(n\) classes of \(H\)
trivial on \(M\). The two group universes and the carrier universe are
independent.

The bijection descends each action to \(G/N\), restricts along the
inverse of \(\phi\), and inflates from \(H/M\). If \(\phi\) sends the
image of a subgroup \(S\subset G\) onto the image of a subgroup
\(T\subset H\), the original class is trivial on \(S\) exactly when
its image is trivial on \(T\).
`continuousIrreducibleQuotientTransport_isTrivialOn_iff` uses the fact
that triviality after precomposition with a group homomorphism is
triviality on the image of the subgroup. This can be applied at each
level of a filtration preserved by the quotient isomorphism.

`ContinuousIrreducibleClasses.TrivialOn.twistEquiv` twists on the quotient
and inflates. The underlying class is the ordinary twist by the pullback
character. `continuousIrreducibleQuotientTransport_twist` shows that the
transport commutes with twisting by a character of \(H/M\) on one side and
its pullback along \(\phi\) on the other. The proof reduces to
precomposition of the scalar character twist on a representative.

The quotient transport abstracts the representation comparison of
Henniart, `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§5.1, p. 512. Its two compatibility statements follow by preservation of
the quotient subgroup images and of the pulled-back characters.

[Inflation equivalence](IrreducibleQuotientEquiv.md) ·
[Group transport](../../VirtualRepresentation/Weil/GroupTransport.md)

`trivialityParameters` records the nonnegative filtration parameters where a class is trivial. `IsomorphismClasses.isTrivialOn_of_le` restricts triviality to a subgroup, and `equivOfSameFibers` identifies the targets of two surjections with the same fibers.
