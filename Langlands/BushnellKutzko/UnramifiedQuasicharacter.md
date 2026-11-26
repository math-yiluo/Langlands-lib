# Unramified quasicharacters and determinant twists

`IsUnramifiedQuasicharacter χ` says that \(\chi:F^\times\to\mathbb C^\times\)
is trivial on the image of \(\mathfrak o_F^\times\). The integer units
form an open subgroup of \(F^\times\). The proof uses the two open
conditions that a unit and its inverse lie in \(\mathfrak o_F\). The
kernel of \(\chi\) thus contains an open neighborhood of the identity,
and the kernel of \(\chi\circ\det\) is open by continuity of the determinant.
`unramifiedTwist π χ hχ` applies `SmoothRep.twist` to this determinant
pullback, in the carrier universe of \(\pi\).

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), the last assertion of (6.2.3) and Lemma (6.2.5),
printed pp. 204–205.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
