# Admissibility of the standard opposite Jacquet representation

This proof implements
`Langlands.Parabolic.StandardOppositeJacquetAdmissibilityStatement.{uF,uV}`.
The prime, p-adic field, supplied topology, rank, block shape and complex
representation carrier retain exactly the statement's quantifiers. The only
representation hypothesis is admissibility. Rank zero is included.

For the unnormalized quotient, the proof first works on the embedded diagonal
Levi. Smoothness descends through the actual radical quotient map. For an
arbitrary open subgroup `L` of the embedded Levi, pull it back to the product
Levi and apply the published small-Iwahori existence theorem. This produces a
compact open ambient subgroup `K` whose Levi intersection `J` lies in `L`.

Choose a strictly contracting upper block-scalar tuple. The published opposite
canonical-lift theorem makes the actual stable-image Jacquet map at its inverse
bijective. Its domain is a submodule of the finite-dimensional space of
`K`-fixed ambient vectors, so its codomain, the `J`-fixed opposite quotient, is
finite-dimensional. The `L`-fixed space embeds into that codomain by inclusion
and is therefore finite-dimensional as well.

The upper modulus pulled back to the embedded Levi has open kernel. Its inverse
has the same kernel, so twisting by the inverse half of this inverse modulus
preserves admissibility. This is precisely the positive upper half-modulus
normalization in `CuspidalJacquetMultiplicity.oppositeJacquet`. Finally the
existing continuous equivalence from the product Levi to the embedded Levi
transports admissibility to that construction's actual product-Levi action.

The proof uses the published opposite canonical-lift, Iwahori existence,
open-kernel twist and continuous group-transport theorems. It supplies only the
standard GL clause. Admissibility for arbitrary refined product-Levi inputs,
the composed quotient, and the complete five-clause statement remain separate
proof obligations.
