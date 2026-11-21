# Finite powers of a one-dimensional formal law

`CommLaw.copies` constructs the product of a one-dimensional commutative formal group law indexed by a finite type. Its coordinate projections recover the addition and inverse of each factor. The group law identities follow by composing the original identities with the projections.

`CommLaw.Hom.toCopies` assembles formal homomorphisms to the factors. The projection and assembly identities give the diagonal ring map on formal endomorphisms. The chain rule shows that each diagonal tangent entry is the tangent scalar of the corresponding factor. `ModuleLaw.copies` applies this to the scalar action to obtain the product of a one-dimensional formal module. The construction supplies finite product coordinates for the framing module in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 A, printed p. 109.
