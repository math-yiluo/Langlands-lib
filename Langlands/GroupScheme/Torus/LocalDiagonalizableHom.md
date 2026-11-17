# Homomorphisms between diagonalizable groups over local rings

This internal prerequisite for the complete-local deformation proof derives
full faithfulness of the diagonalizable-group construction over a local ring.
It does not require the ring to be a field or the character groups to be free
or finitely generated.

The argument extends the published proof in `DiagonalizableCharacterProof`.
The universal value of a natural character is group-like, so its coefficients
are pairwise orthogonal idempotents summing to one. The published local-ring
idempotent lemma in `Langlands.Algebra.HopfPointConnected` implies that exactly
one coefficient equals one and all others equal zero. Thus every natural
character is evaluation at a unique character-group element.

Apply this result to each coordinate of a group-scheme homomorphism. Its group
law makes the chosen character-group function additive. The published
`Diagonalizable.pointsEquiv_restrictMap` formula and equality on all test
schemes identify the resulting homomorphism with the original one. Uniqueness
of the coordinate evaluations proves injectivity.

`characterHomEquiv R M N` packages this classification as the equivalence
`(N →+ M) ≃ Hom(D_R(M), D_R(N))`. Its forward map is the published
`Diagonalizable.restrictMap`.

The canonical `Diagonalizable.baseChangeIso` preserves character-valued
points on every test scheme. Together with naturality of
`baseChangePointsEquiv`, this proves `baseChange_restrictMap`: the comparison
intertwines a base-changed restriction map with the restriction map for the
same homomorphism of character groups. No local-ring hypothesis is needed
for this naturality identity.

If both base rings are local, conjugating the base-change map on
homomorphisms by the canonical comparisons identifies it with the two
character-group classifications. Thus `baseChange_hom_bijective` proves
bijectivity of the actual base-change functor on these Hom sets. The base
map is arbitrary; it need not be injective, surjective, or local. In
particular this applies to the residue field and Artinian quotient rings
of a local ring.

This is derived content from the published group-algebra and pointwise
interfaces, with the same proof structure as the published field case. The
local-ring version supplies the split-group step used in Conrad (2014),
Theorem B.3.2(2), p.289. It alone does not prove that an Artinian deformation
is diagonalizable or algebraize any compatible adic system.
