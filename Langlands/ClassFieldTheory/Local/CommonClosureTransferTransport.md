# Actual common-closure Weil and Galois transfer transport

Worker 125, using Worker 170's prescribed-field comparisons.

The actual Weil projection at each finite intermediate field has dense
image in its literal fixing subgroup: conjugate the published standalone
projection by the prescribed Weil and Galois equivalences.

The actual coset-product transfer squares on Weil and Galois abelianizations
then commute with projection. The subgroup over the larger intermediate
field is the preimage of its Galois fixing subgroup. Apply the dense-map
transfer naturality theorem to this preimage, and rebracket each nested
subgroup through the actual subtype equivalence. This proof uses the
constructed transfers throughout and applies to nonnormal intermediate
fields.

`galoisTransferHom` is the actual Galois transfer after the unit map induced
by a supplied candidate family. It is a derived construction used to state
the remaining arithmetic square. No arithmetic transfer law is assumed by
the preceding group-theoretic comparison.

The Weil-to-Galois abelianization projection is injective at each
intermediate field. This follows from the published standalone injectivity
and the two prescribed-field quotient equivalences. It therefore reflects
equality of the transfer values. Cancellation of each candidate with its
inverse proves `transferRelation_iff_galoisTransferRelation`: the actual
Weil transfer law is equivalent to the Galois transfer square for any
candidate family. The forward implication uses transfer naturality; the
reverse uses it together with injectivity. This is a reduction, and the
arithmetic Galois transfer relation remains to be proved for the constructed
family.
