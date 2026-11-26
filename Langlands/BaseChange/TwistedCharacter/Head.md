# Twisted traces and the canonical head of a smooth representation

The kernel defining the canonical head is preserved by a twisting
isomorphism. For an irreducible quotient map, pull that map back through
the group automorphism and compose it with the twisting isomorphism.
This gives another irreducible quotient map. It kills every vector in
the head kernel. Applying the same argument to the inverse gives equality
of the mapped kernel and the original kernel.

For an admissible finite-length representation, restrict the twisting
operator to the invariant kernel and descend it to the head. Additivity
on the resulting short exact sequence gives the twisted trace of the head
as a difference. The kernel trace belongs to the span of the traces of its
stable irreducible subquotients by `twistedDistribution_mem_of_finiteLength`.
If the head is irreducible, Schur comparison transports the head trace to
the designated irreducible quotient with any twisting isomorphism.

This is the head step in the standard-module trace expansion used in the
proof of Henniart–Lemaire (2011), II.5.10 and II.5.13. An application to a
standard module needs a classification of the representations occurring in
its head kernel.
