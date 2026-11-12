# Finite Galois restrictions of geometric profinite reciprocity

This internal construction uses a specified embedding of a finite Galois
field into the base field's algebraic closure. The kernel of actual
restriction fixes precisely the embedded image field. This kernel is open,
so restriction is continuous and descends to the closed-commutator quotient
with values in the finite Galois group's algebraic abelianization.

`closureFiniteAbelianRestriction_geometric` identifies the finite
restriction of every map satisfying `GeometricProfiniteReciprocityRelation`
with `abelianizedArtinSymbol` evaluated at the inverse unit. No abelianity
of the chosen finite extension is required.

The proof takes the preimage of the finite commutator subgroup under
restriction. This is open, normal, and contains all absolute-Galois
commutators. Its fixed field is therefore an actual finite abelian
extension. Galois correspondence places this field inside the embedded
image of the chosen finite extension; the image-field equivalence supplies
its embedding back into that extension.

Restriction to this abelian field induces an injective map out of the
chosen finite Galois abelianization. Indeed, a finite automorphism
restricting trivially lifts to an absolute automorphism in the defining
open subgroup, so its abelianization is trivial. Actual restrictions
compose through these embeddings. The proved normal-restriction law for
`abelianizedArtinSymbol` then reduces the desired equality to this abelian
field. There, the published uniqueness theorem for the geometric finite
Artin system identifies every normalized profinite map with the concrete
geometric finite family.

The proof uses only published finite-family uniqueness and the derived
finite-symbol restriction law. It does not assume the inverse-cup
character comparison or a transfer reciprocity law. All carrier fields
remain in the arbitrary universe quantified by the theorem.
