# Finite Artin character symbols on arbitrary Galois abelianizations

This internal construction extends the published finite carry-symbol
construction to the actual group abelianization of any finite Galois
extension of a p-adic field in the same carrier universe. The extension
need not be abelian.

The order of the abelianization divides the finite Galois group order,
which equals the field degree. The existing finite abelian duality
therefore applies with values in the multiplicative form of
`ZMod [D : F]`. Pulling a character back through the actual abelianization
projection and applying the published `symbolValue` gives a homomorphism
on the character group. Duality constructs `abelianizedArtinSymbol`.
The existing additivity of the carry symbol in the base-field unit proves
that this construction is a group homomorphism.

The evaluation formula identifies every character value with its original
carry symbol. When the finite Galois group is abelian, character separation
proves that the new map is the existing `artinSymbol` followed by the
actual abelianization projection.

Scaling the cyclic character into `ZMod [D : F]` extends the evaluation
formula to every character modulus dividing the degree. For a finite
Galois tower, inflation of the carry class preserves its relative
invariant. Applying this identity to all characters proves that
`abelianizedArtinSymbol` commutes with the actual Galois restriction map.
The tower argument does not require either Galois group to be abelian.

This file supplies no assertion that this map equals inverse-cup
reciprocity, and no transfer law, norm-kernel theorem or Weil reciprocity
existence theorem. Those are separate mathematical comparisons.
