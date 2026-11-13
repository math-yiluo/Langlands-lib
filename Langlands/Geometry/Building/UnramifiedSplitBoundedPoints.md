# Bounded split-torus points in every unramified zero datum

Internal derived helpers for the integral torus clause, at arbitrary universe
`u`, over a nonarchimedean local field `F`. Scalar unit norm
surjectivity specializes the published spectral-valuation norm theorem to the
unramified closure as base and the supplied finite Galois field as both the
extension and its normal closure. Equivalence of normalized and spectral
valuations identifies the units.

The zero subgroup contains the simply connected cover image and is therefore
normal by the published commutator-cover theorem. A closed split subtorus
extends to a maximal split torus; rational conjugacy identifies this with the
maximal split torus inside the datum's maximally split maximal torus. Functoriality
of the character-valuation kernel, split bounded norm surjectivity and norm
naturality put the conjugated image into the datum's torus norm image. Normality
removes the conjugation. No independence theorem for zero data is assumed.

Precisely, `map_split_characterValuationKernel_le_zeroPoints` assumes a
connected reductive group over the maximal unramified closure, an arbitrary
`UnramifiedZeroDatum` for that group, and a closed split subtorus. It includes
the image of the character-valuation kernel for the normalized valuation in
that datum's zero subgroup. The subtorus need not be maximal.
`splitBoundedPointMap` is the actual point homomorphism with domain restricted
to this kernel and codomain restricted to the zero subgroup. Its underlying
value is the rational-point map of the supplied inclusion.

All assertions are derived from published Library constructions and theorems;
no new external source assertion or additional building axiom is used. In
particular `normal_zeroPoints` uses the simply connected cover and containment
already supplied by the datum. It asserts normality, not equality between the
zero subgroups of different data.
