# Evaluation of Harris scheme cocharacters

This module is an internal specialization of the published affine cocharacter
transport and Harris Galois-cocharacter constructions. It introduces no
literature convention or additional descent datum.

For a rational group scheme G, `rationalComplexCocharacterValue` evaluates an
actual cocharacter of its complex pullback on a unit u of C, returning an actual
C-valued point of G over Spec Q. It is the generic `affineCocharacterValue`
expressed with the named `rationalComplexBaseMap`. Its transport theorem proves
that evaluation of the cocharacter transported along Spec(s) equals the existing
affine point action of s on evaluation at s inverse of u, for every Q-algebra
automorphism s of C.

For central simple unitary data D, `D.directComplexCocharacterValue` specializes
that evaluation to `D.rationalBaseChange rationalComplexBaseMap`.
`directComplexCocharacterValue_transport` proves the same formula with output
action `D.complexPointGaloisAction`. The proof applies the generic rational
transport theorem; the named Harris point action agrees definitionally with the
generic affine action.

The iterated real-to-complex model is connected to this direct rational pullback
by the already constructed `D.complexDirectGroupSchemeIso`.
`D.complexCocharacterValue` evaluates an actual cocharacter of the iterated model
by postcomposing with that isomorphism and applying direct-model evaluation.
`complexCocharacterValue_comparison` records this definition as an equality.
`complexCocharacterValue_galois_comparison` says that evaluating
`D.galoisCocharacter s χ` equals direct-model evaluation of the generic transport
of `χ` postcomposed with the comparison isomorphism. Its proof applies congruence
of direct-model evaluation to the published `galoisCocharacter_comparison`.

These declarations supply an actual point evaluation and the stated comparison
identities. This module does not contain the combined iterated-model Galois
evaluation theorem, its algebra-coordinate corollary, matrix-factor transport,
or a reflex-stabilizer comparison. Those remain separate formalization
obligations. In particular no equality of scheme morphisms is inferred from
field-valued points.
