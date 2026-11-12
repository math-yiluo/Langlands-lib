# Finite Galois restrictions of actual fixing subgroups

Worker 125. Internal infrastructure for Task 4919.

For a finite Galois intermediate field containing a specified finite
intermediate base, `finiteRestrictionHom` restricts each actual ambient
fixing automorphism to that finite field. Its scalar structure uses the
literal field inclusion. The intermediate base need not be normal over the
original base. The action formula follows from restriction of algebra
automorphisms. Its kernel is precisely the actual subgroup fixing the
finite field, so it is open and restriction is continuous. Surjectivity is
the extension theorem for automorphisms of a normal subextension.

The companion `discreteAbelianizationEquiv` identifies the quotient by
closed commutators with the algebraic abelianization for a discrete group.
Composing it with the induced finite restriction gives
`finiteAbelianRestriction`, with the stated action on quotient generators.
This enables finite arithmetic reciprocity statements expressed in
algebraic abelianizations to be compared with the actual topological
common-closure quotients.

The construction is derived from the Library subgroup, algebraic
restriction, and abelianization interfaces and Mathlib's normal-tower and
automorphism-extension results. No arithmetic reciprocity law is assumed.
