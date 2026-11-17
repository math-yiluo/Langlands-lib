# Images of unipotent parts of solvable groups

Worker 883.

`PreservesUnipotentParts q` says that a supplied smooth closed image of a
greatest unipotent subgroup under `q` is again a greatest unipotent subgroup.
The image is specified by a surjective homomorphism `f` and the equation
`i ≫ q = f ≫ j`.

`QuotientUnipotentPartImage.preservesUnipotentParts` proves this for a
surjective homomorphism between smooth connected solvable affine groups over
an algebraically closed field. The proof does not require flatness of the
ambient homomorphism.

The supplied image is connected by surjectivity. The homomorphism onto it is
flat by the published dominant-homomorphism flatness theorem, so unipotence
descends through it by coefficient representations. Thus the supplied image
lies in a greatest unipotent subgroup of the target.

For the reverse inclusion choose a maximal torus of the source. Its actual
schematic image is a split torus. Every rational point of the target's
unipotent part lifts to a rational point of the source, which factors as a
unipotent point times a torus point by the published solvable factorization.
The first factor maps into the supplied unipotent image. Consequently the
image of the torus factor belongs both to the torus image and to the target
unipotent part. The published trivial-intersection theorem for a split torus
and a unipotent subgroup forces that factor to be the identity. Every
rational point of the target unipotent part therefore belongs to the
supplied image.

Containment on rational points implies containment on every test scheme
because the source of the containment is smooth and locally of finite type,
and the subgroup being tested is closed. Composing with the target
unipotent part's greatestness proves the required greatestness.

This is derived infrastructure for the equality of unipotent parts used in
Milne 2017, Proposition 17.20 (printed p.357). It uses the published torus
image theorem, rather than maximal-torus image preservation, and hence
introduces no dependence on the torus clause of the quotient-image target.

Source: James S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Proposition 17.20 and Theorem 16.33. The implemented proof route is described
above.
