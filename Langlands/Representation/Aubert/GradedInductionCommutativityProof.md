# Commutativity of actual graded normalized induction

This internal proof derives commutativity of the published multiplication from
the positive-rank two-factor constituent matching theorem and the actual
rank-zero tensor models. The final theorem is `gradedMultiplication_comm`,
for every supplied `BinaryProductExactnessStatement F T` witness and independent
field and carrier universes. It compares the actual `gradedMultiplication`,
with no additional representation-theoretic parameters.

`hom_ext_irreducible` uses the published bijective irreducible realization of
the exact finite-length Grothendieck group. This accounts for the full short
exact relations, including nonsplit sequences. Positive irreducible products
are compared by the published constituent theorem on the binary shape; the
swapped shape is explicitly identified with the reversed binary shape after
the commuted-sum rank cast. Transported composition series then identify exact
classes, and the homogeneous inclusions eliminate the total-rank cast.

The positive input uses smooth contragredients, Gelfand--Kazhdan, cuspidal
embedding and finite length of normalized products, as detailed by
`Classification.TwoFactorProductConstituentCommutativityProof`. No
classification independence is claimed.

`zeroLeftProductEquiv` retains every vector in the arbitrary rank-zero
factor. It composes the actual left-zero tensor equivalence, the tensor
commutor, and the pulled-back inverse of the actual right-zero tensor
equivalence. Intertwining on pure tensors reduces to composition of the
entry-preserving rank reindexes. This includes rank (0,0): neither factor
is replaced by the unit line. `gradedInclusion_eq_of_rank_equiv` then gives
commutativity for arbitrary finite-length object classes with a zero first
rank; symmetry treats a zero second rank.

`irreducible_classes` combines these boundary comparisons with the positive
comparison. `gradedMultiplication_comm` compares the multiplication with its
linear-map flip: direct-sum extensionality reduces the first variable to a
rank, and `hom_ext_irreducible` reduces it to an actual irreducible object.
The same two reductions in the second variable reach `irreducible_classes`.
Thus the conclusion holds for every finite-length object and every virtual
class in the full graded exact Grothendieck group.

This is a derived consequence of the existing Library constructions and proofs,
and claims no polynomial presentation or Aubert comparison. The only local
additional equivalences are equality transport for binary block families,
rank transport for product induction, and the actual zero-rank tensor
commutor. The explicit half-modulus normalized-induction conventions, supplied
field topology and saturated carrier universe remain those of the imported
construction.
