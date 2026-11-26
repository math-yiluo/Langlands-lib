# Exact norm lifts on open cosets

The inverse affine norm chart supplies exact lifts on a neighborhood of the
identity. The rational torus is locally compact by `WeylTorus.isClosed_val`.
Van Dantzig's theorem gives a compact open subgroup in this neighborhood.
For each of its cosets that meets the regular norm domain,
choose one point of that domain and one exact lift of the point. Multiply
this fixed lift by the identity-neighborhood lift of the remaining factor
in the subgroup. The rational norm homomorphism verifies the exact norm.

On each coset, multiplication by the fixed rational representative changes
the affine Lie coordinate by an affine linear map. Composing it with the
strictly differentiable inverse chart gives the matrix representative of
the lift near every point. Right translation by the inverse of the lift at
the center normalizes the representative to the identity there.

The local construction uses the submersive torus norm in
Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle*, §II.2.10, printed p. 71. The source identifier
is `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
and the retained PDF SHA-256 is
`7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
