# Finite projective rank-one modules give affine line sheaves

For a finite projective module with rank one at every prime, freeness and the rank spread from the stalk to a principal open containing the prime. Over that open the sections of the associated sheaf are the localized module and admit a line basis. The affine reconstruction of the restricted quasi-coherent sheaf transports that basis to an actual local sheaf isomorphism with the structure module.

This supplies the local trivializations for the homogeneous tangent components in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 B, printed p. 110 (PDF p. 4).

`affineLineTrivialization` constructs the isomorphism on a specified principal open. The line-sheaf criterion uses `Langlands.Algebra.isLocallyFreeRankOne_tilde_of_rankAtStalk_eq_one`.
