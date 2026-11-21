# The number-field Hasse kernel in type G₂

`Langlands.GroupScheme.NumberFieldTypeG2HasseStatement` asserts that a locally trivial cocycle with coefficients in an actual simply connected absolutely almost-simple group of numbered type `G₂` over a number field is trivial. Both the global cocycle and its trivialization live on the given finite Galois cover. The local hypothesis uses the pullback of that cover at every completion. `numberFieldTypeG2Hasse` proves the statement for every universe.

The actual Cayley presentation realizes the group as the automorphism matrices of a Cayley datum. Matrix Hilbert 90 produces an invertible matrix whose Galois discrepancies are the represented cocycle. The transported Cayley datum descends to the number field, and the matrix intertwines the descended and original multiplications over the cover field.

Over each completion, choose a finite Galois comparison field containing compatible copies of the completion and of the cover field. A local cochain corrects the matrix by a Cayley automorphism. The corrected matrix is fixed under the relative Galois action, so it descends to an isomorphism matrix over the completion. It identifies the extended Cayley norms, which are the tensor extensions of the original norms.

The number-field quadratic isometry theorem now makes the two norms isometric over the number field. The Cayley norm classification gives an algebra isomorphism over that field. Using it to correct the global matrix produces an automorphism matrix. The closed representation identifies it with a group point on the original cover, where it satisfies the cocycle's coboundary identity.

The Cayley presentation and norm classification are from Knus, Merkurjev, Rost and Tignol, *The Book of Involutions*, Theorem 26.19 (printed p. 373, PDF p. 396) and Theorem 33.19 (printed pp. 460–461, PDF pp. 483–484). This proof derives the Hasse statement from those comparisons and `numberFieldQuadraticIsometry`.
