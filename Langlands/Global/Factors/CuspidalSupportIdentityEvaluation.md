# Cuspidal block evaluations from the identity coefficient

`compactFiniteCoefficientEvaluation` precomposes an identity coefficient
map with finite and compact translations of the same source. For each
place the compact translation can be restricted to tuples with identity
at that place. A place translation and a place Lie generator commute
with both of these complementary actions.

The real and complex evaluation constructors use this commutation to
transport the identity compact and normalized Lie equations to every
complementary compact and finite point. Every full compact point
factors as a complementary point times an element of the chosen place.
The assumed separation on full compact and finite translates therefore
gives separation for the local Jacquet probes. The full intertwiner
supplies the quotient map's compact and Lie compatibilities.

The construction uses the actual automorphic operator algebra and the
factorization in `ArchimedeanOperatorPlaceComplement`. It supplies the
place evaluation families for `CuspidalSupportProjectedBlocks` from the
identity coefficient of a single block projection.
