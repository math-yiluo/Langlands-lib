# Z-extensions of actual reductive groups

This module gives the group-scheme meaning of a z-extension used in the
construction of the Kottwitz homomorphism. Its source is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §11.4 and Construction 11.4.1,
printed pp. 428–429 (PDF pp. 459–460), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024 make no change to §11.4.

`HasSimplyConnectedDerivedGroup G` means that an actual closed inclusion
`d : D → G` represents the Library's full derived subgroup functor, and `D`
is algebraically simply connected in the existing Library sense. This is an
internal packaging of the phrase “the derived subgroup is simply connected”.

`IsZExtension i p` describes actual maps `Z → H → G`. It requires that `Z`
be an induced torus using `IsInducedTorus`, that its inclusion be closed and
central, that both ambient groups be connected reductive, that the derived
subgroup of `H` be simply connected, and that `p` be the represented fppf
quotient by the full image subgroup functor of `Z`. The quotient predicate
requires flatness, surjectivity, local finite presentation, and equality with
the full scheme kernel on every test scheme. It therefore expresses the
exact sequence as an fppf sequence; it does not assume surjectivity on the
rational points of the ground field. Centrality, automatic for the source
sequence in KP, is recorded explicitly as a mathematical property.

`ZExtension G` packages these groups, maps and properties as choice data.
It contains no homomorphism on point groups and no assertion about the kernel
of a Kottwitz map. It works over every field, with no characteristic,
splitting or quasi-splitting restriction. General existence is the separate
proposition `ZExtensionExistenceStatement`; this definition alone asserts
no existence and proves no structural theorem.
