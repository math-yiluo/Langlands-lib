# Proof of the finite tame inertia structure

`Langlands.Ramification.Padic.finiteTameInertiaStructure` proves
`FiniteTameInertiaStructureStatement`. It uses the existing lower
ramification groups of the supplied p-adic topology.

For the first lower group, the proof uses
`pow_mem_lowerGroup_succ_of_natCast_mem`: taking the `p`-th power in a
positive lower group moves the element to the next lower group, since the
cast of `p` belongs to the maximal ideal. After `k` steps the `p^k`-th
power lies in the `(k+1)`-st lower group. These groups terminate, so every
element of the first lower group has `p`-power order. The helper proving
this needs only termination and the maximal-ideal membership, not the
finite Galois description of the quotients.

For the tame quotient, choose a uniformizer and use the published
`uniformizerCharacter` of the zeroth lower group. In its kernel, the
uniformizer moves by an element of the square of the maximal ideal.
Surjectivity of Frobenius on the finite residue field then implies
membership in the first lower group by `mem_lowerGroup_one_of_frobenius`.
Conversely, the image of an element of the first lower group has `p`-power
order, and a field of characteristic `p` has no nontrivial such roots of
unity, by the formula for `(x - 1)^(p^k)`. Thus the character into residue
units has exactly the indicated kernel.

The quotient by this kernel embeds in residue units. The finite subgroup
of the units of a field is cyclic, and its order divides the residue
unit-group order, the residue cardinality minus one. The residue
cardinality is a positive power of `p` with positive exponent, so its
predecessor, and hence the order of this quotient, is prime to `p`.
