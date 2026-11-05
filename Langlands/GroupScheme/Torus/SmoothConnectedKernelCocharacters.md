# Integral cocharacters of split-torus quotients with smooth connected kernel

Worker 1435. Internal supporting construction for the cocenter quotient proof.

For an epimorphism of split tori over any field in universe `u`, a smooth
connected full scheme kernel makes postcomposition surjective on the actual
integral cocharacter lattices. The theorem retains the full kernel, including
possible infinitesimal phenomena before the smoothness assumption is applied.

`IsSplitTorus.cocharacterLiftOfSmoothConnectedKernel` chooses one integral
source lift for each target cocharacter under exactly these hypotheses.
`cocharacterLiftOfSmoothConnectedKernel_comp` proves that postcomposition
maps this chosen lift to the prescribed cocharacter. The choice uses the
surjectivity theorem below; no uniqueness or additivity of this choice is
asserted.

The implementation uses the published identification of the actual kernel
with the diagonalizable group whose character group is the full quotient of
the source character lattice by the image of pullback. Smoothness and
connectedness make its affine scheme integral. The group algebra is therefore
a domain; its monomials are linearly independent in its fraction field. The
published torsion argument makes the finitely generated quotient character
group torsion free, and hence free over the integers.

Projectivity splits the map to this quotient. Subtracting the section component
constructs a retraction onto the image of character pullback. Since the original
homomorphism is epic, pullback is injective. Its inverse on its image therefore
gives a left inverse on character lattices. Composing any integral target
cocharacter functional with that left inverse extends it to the source
character lattice. Perfectness of the split-torus integral pairing realizes
the extension as an actual source cocharacter. Character pairings detect that
its image is the prescribed target cocharacter.

This is an internal argument from the published kernel presentation,
smooth-connected integrality, torsion-freeness, projectivity and the coordinate
perfect pairing. It neither asserts nor assumes that the intersection of a
maximal torus with the actual derived subgroup is smooth and connected;
that geometric input remains separate in the cocenter application.

The perfect-pairing step reuses the existing arbitrary-field theorem
`CocharacterUniformizer.latticePairing_isPerfPair`.
