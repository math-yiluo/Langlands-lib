# The Kottwitz kernel for a group with simply connected derived subgroup

This internal reduction implements the simply connected derived-group case in
the proof of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 11.5.4, printed page 431 (PDF page 462).

The theorem is conditional on `TorusKottwitzKernelStatement` (Proposition 11.1.5)
and `SimplyConnectedDerivedKottwitzStatement` (the cocenter construction of
Section 11.5). It does not prove either input.

Choose an actual cocenter over the original coefficient field. Its base change
remains the quotient by the full derived subgroup, and that derived subgroup
remains simply connected. `CocenterZeroReduction` therefore identifies the
supplied zero subgroup with the inverse image of the cocenter's norm-defined
torus subgroup. The torus kernel input identifies that subgroup with the torus
Kottwitz kernel on the original torus's coefficient points. Naturality of
`baseChangeCoeffEquiv` makes the two point conventions agree.

Finally, the cocenter square in the map specification and injectivity of its
target map identify this inverse image with the simply-connected-derived
Kottwitz kernel. No compatibility between independently selected maps over
different base fields is assumed. The conclusion holds for every supplied
unramified zero datum.
