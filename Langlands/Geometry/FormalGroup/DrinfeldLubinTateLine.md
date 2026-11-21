# The Lubin–Tate line over a Drinfeld residue coefficient field

Finite étaleness of the embedded integer subfield identifies its maximal ideal with the extension of the original maximal ideal. Thus the original uniformizer is a nonzero generator there. The standard Lubin–Tate construction over this integer ring can be reduced through the chosen residue embedding.

`drinfeldLubinTateCoefficients` acts by the reductions of all the integral scalar endomorphisms. Its tangent character is the chosen residue map, and the original scalar ring acts by restriction. The uniformizer acts by the power of the coordinate whose exponent is the embedded field's residue cardinality. This follows by reducing its standard polynomial `πT + T^q`.

The construction specializes Lubin and Tate, *Formal Complex Multiplication in Local Fields* (1965), §1, Theorem 1, printed p. 382. The coefficient ring is the one in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 B, printed p. 110.
