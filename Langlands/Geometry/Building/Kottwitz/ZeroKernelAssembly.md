# Assembly of the zero-kernel reduction

`UnramifiedZeroKernelReductionStatement` is an internal conditional reduction
following the two group-theoretic steps of the proof of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.4,
printed page 431 (PDF page 462). It states the implication from
`TorusKottwitzKernelStatement`, `SimplyConnectedDerivedKottwitzStatement`,
`ReductiveKottwitzExistenceStatement` and
`ZExtensionKottwitzKernelSurjectivityStatement` to the existing
`UnramifiedZeroKernelStatement`, at arbitrary universe `u`.
`unramifiedZeroKernel_of_torus_zExtension` proves this implication. The
prerequisites remain explicit assumptions; this module does not prove them.

The conclusion retains every compatible field of definition `k`, every
connected reductive `k`-group and every actual unramified zero datum. The maps
are the existing constructed Kottwitz homomorphisms. The subgroup is the
existing supremum of the simply connected image and the torus norm subgroup,
as specified by that datum.

First, subgroup images commute with `baseChangeCoeffEquiv`, since it is an
equivalence natural in the group-scheme map. This transfers an image equality
on the original group's coefficient points to rational points of its actual
base change.

The full scheme-theoretic kernel of every actual z-extension is central and
is a torus. Centrality follows from the full-kernel equality in its fppf
quotient condition. Its closed induced-torus representative is isomorphic to
the actual kernel, so its splitting field supplies the torus property.
These facts persist under base change to the unramified closure.

Choose a z-extension using the reductive map existence input, and choose an
unramified zero datum for its source using published derived-cover existence.
The source has simply connected derived subgroup. The accompanying
`SimplyConnectedZeroKernelReduction` module uses the torus kernel statement
and the simply connected derived map specification to identify its zero
subgroup with its Kottwitz kernel. The reductive specification identifies the
source's two constructed Kottwitz maps. The proved central torus-kernel image equality
then maps this zero subgroup onto the supplied target zero subgroup. The
z-extension kernel-surjectivity input maps the source Kottwitz kernel onto
the target kernel; only the first conjunct of that input is used. The
coefficient-point comparison makes these two image equalities refer to
exactly the same point map.

This gives the unramified kernel equality for every allowed field of
definition and every existing zero datum. Finally `zeroKernel_of_unramified`
pulls it back using the two descent inputs to obtain the exact rational
`ZeroKernelStatement`. This last corollary,
`zeroKernel_of_torus_zExtension`, additionally assumes
`ReductiveKottwitzDescentStatement` and `UnramifiedZeroDescentStatement`.
All six inputs remain explicit, so it is a conditional implication and
does not establish the unconditional rational `ZeroKernelStatement`. No compatibility
between maps chosen over different fields of definition is needed.
