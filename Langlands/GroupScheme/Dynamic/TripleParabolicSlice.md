# A rational lifting neighborhood for three parabolics

`exists_open_tripleParabolic_rationalLift` supplies an open neighborhood of
the identity in the cube of a smooth connected affine field group. The
input is a split torus and three cocharacters summing to zero. Every root
must vanish on all three or be negative on exactly one, and the roots
vanishing on the first difference must vanish on all three. Every rational
point `(g₀, g₁, g₂)` of the neighborhood admits a common rational left factor
`h` with `h⁻¹ gᵢ` in the corresponding dynamic parabolic.

The slice multiplies two opposite dynamic unipotent factors, for the first
difference and its negative, followed by an independent factor from each
of the three parabolics. Equality of the three products puts the ratio of
the two common left factors in the triple intersection, which is the
dynamic centralizer of the difference. The opposite unipotent and
centralizer intersection identities then give injectivity on test
schemes. On tangent spaces the common left factor can match the component
of each input in the weights excluded from its parabolic. The sign
hypotheses make these prescriptions compatible, and the difference
assigns those weights to the two opposite unipotent factors. Thus the
slice is smooth at the identity. Its smooth locus maps by an open
immersion, so points in the image lift over the field itself.

The slice implements the simultaneous conjugation step for the
three-parabolic construction in Platonov and Rapinchuk, *Algebraic Groups
and Number Theory* (1994), §6.8, printed p. 372.
