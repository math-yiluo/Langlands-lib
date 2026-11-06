# Archimedean triviality on included CM idele norms

This internal helper proves that the normalized weight-one infinity character
kills the norm of every idele for a CM field over its maximal real subfield,
after including the norm back into the CM field. The norm and inclusion are
the Library's actual continuous maps on ideles.

`ideleInfinityCharacter t` pulls the normalized infinity character back along
the projection from all ideles to their archimedean factor. For a pure
weight-one type, `ideleInfinityCharacter_complexConj` proves inversion under
the actual arithmetic CM conjugation, on every idele.

The proof of `infiniteAdeleNorm_cm_mul_conj` first writes the algebraic norm of a
field element as the product with its arithmetic conjugate. The quadratic
Galois group consists of the identity and complex conjugation, as follows from
its cardinality and the nontriviality of conjugation. The principal norm
formula then proves the corresponding equality on the diagonal in the infinite
adele ring. Density of that diagonal and continuity give the identity on all
infinite adeles.

`ideleInfinityCharacter_included_norm` projects the included idele norm to this
identity, applies the character, and cancels the two inverse values. The proof
uses only the infinite norm formula; it needs no finite norm decomposition.
`ideleInfinityCharacter_finite` gives triviality on finite ideles, since their
infinite projection is one.

These are archimedean compatibility results. They do not establish the finite
arithmetic kernel condition or the existence of a global Hecke character.
