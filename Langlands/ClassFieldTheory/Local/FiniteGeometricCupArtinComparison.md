# Geometric inverse-cup comparison and finite Artin transfer

This internal module gives an alternative explicit comparison premise and proves
that it suffices for the same actual finite Artin transfer square. It does not
prove either inverse-cup comparison, identify which sign is correct, or prove the
unconditional common-closure reciprocity target. The existing arithmetic
comparison proposition and all its consumers remain unchanged.

`FiniteGeometricCupArtinCharacterComparison` quantifies every prime, every p-adic
field `F` in the stated arbitrary universe, every finite Galois extension `D/F`
in that universe, every positive fundamental class for the exact canonical
relative invariant `FiniteArtinSymbol.relInv F D`, every certificate that its
degree-minus-two cup is bijective, every character of the actual Galois group
into `Multiplicative (ZMod [D:F])`, and every base-field unit. It asserts that
evaluating `geometricReciprocityOfCup` on that unit's actual norm class gives the
published positive carry value `FiniteArtinSymbol.symbolValue`. No abelian
Galois-group assumption is made. The geometric inverse cup here is the inverse
of arithmetic inverse cup in the actual Galois abelianization, as defined in
`TateAbelianization`.

Assuming this proposition, `geometricReciprocityOfCup_eq_symbol` proves equality
with the concrete `abelianizedArtinSymbol`. The implemented proof compares all
characters into the stated cyclic target, uses the existing carry-symbol
evaluation theorem, and applies finite character separation.

`arithmeticTransfer_of_geometricCupComparison` then proves that literal field
inclusion carries arithmetic carry symbols to the genuine finite-coset transfer
in the actual Galois abelianizations. The top field is finite Galois over both
base fields, and the middle field need not be normal over the lower base. The
proof reuses the chosen positive fundamental classes, their proved restriction
law and cup bijectivity from `FiniteArtinTransferReduction`, applies the published
geometric inverse-cup transfer square, and rewrites both inverse-cup values by
the conditional comparison.

Finally, `geometricTransfer_of_geometricCupComparison` proves that same transfer
square for the existing `geometricSymbol`, which precomposes the arithmetic
carry symbol by unit inversion. The proof evaluates the arithmetic square at
the inverse unit and uses that field inclusion preserves inverses.

The provenance is internal: the module combines the actual constructions and
proved conditional transfer theorems from `FiniteCupTransfer`,
`FiniteAbelianizedArtin` and `FiniteArtinTransferReduction`. Its new comparison
is an unproved proposition formulated to keep the two possible inverse-cup
conventions explicit. Establishing the appropriate comparison and passing
from finite transfer to the full common-closure system remain separate
obligations.
