# Permuted bases and the induced-torus lattice criterion

Author: Worker 1642.

This internal linear-algebra construction supports the fundamental-weight route
to `SplitTorusCentralizerCocenterInducedStatement`. It proves the lattice
transport step; it does not prove the geometric or root-datum prerequisites.
The results are derived directly from Mathlib's basis and representation APIs
and the Library definition `IsInducedTorus`.

`Langlands.PermutationBasis.map_permuted` transports a basis through a linear
equivalence that intertwines two representations. Applying the equivalence
to each supplied basis-permutation equality proves the result.

For a group representation preserving a basis setwise, `indexEquiv` constructs
the corresponding permutation of the index set. Its inverse comes from the
inverse group element, and linear independence makes the chosen indices unique.
`indexAction` proves that these permutations form a group homomorphism. This
construction assumes a nontrivial coefficient ring so basis vectors have unique
indices. No finiteness or nonempty-index assumption is needed.

`complementSpan` is the span of basis vectors outside a chosen set of indices.
`mem_complementSpan_iff` identifies it with the vectors whose coordinates on that
set vanish, using Mathlib's basis-support characterization of a subfamily span.
`complementBasis` is the restricted basis, with its ambient values recorded by
`complementBasis_apply`. Applied to a fundamental-weight basis and the indices
of a Levi root system, these constructions describe the abstract candidate
for a cocenter character lattice. The identification with the actual character
lattice remains a separate obligation.

`complementRangeEquiv` identifies the domain of a supplied injective linear map
with this complement span, provided its image is exactly that span.
`pullbackComplementBasis` then pulls the restricted basis back to the domain.
`map_pullbackComplementBasis` proves that these pulled-back vectors map to the
original complementary basis vectors.

`pullbackComplementBasis_permuted_of_twist` handles the Weyl correction in the
proposed cocenter argument. It assumes representations on the source and ambient
lattices, an equivariant injective map between them, and, for each group element,
a linear twisting operator on the ambient lattice that fixes the entire image of
the source. If the twisted ambient action preserves the complementary basis,
the actual source action permutes the pulled-back basis. To prove this, insert
the twisting operator in the image of a transformed source vector, use
equivariance, and apply injectivity. No group law for the twisting operators is
assumed or claimed. `pullbackComplementBasis_permuted` is the identity-twist
specialization.

`Langlands.GroupScheme.isInducedTorus_of_equivariant_basis` works with the
existing character lattice and the existing Galois representation. It assumes
a finite Galois field extension in the same universe as the base field, an
actual split-torus base change, an auxiliary integral lattice with a permuted
basis, and an equivariant linear equivalence from that lattice to the actual
character lattice. It transports the basis and supplies exactly the witnesses
in `IsInducedTorus`. It adds no field characteristic restriction.

`Langlands.GroupScheme.isInducedTorus_of_twisted_complement` packages the
character-embedding version for the existing Galois action. The injective map
from the actual character lattice, its exact complement-span image, its
equivariance, the fact that every correction fixes that image, and the
permutation of complementary basis vectors are explicit hypotheses. The proof
uses the pulled-back complementary basis as the witness in `IsInducedTorus`.
In particular, the module does not assert the existence of a parabolic, a
fundamental-weight basis, any Weyl corrections, or the supplied character map.
