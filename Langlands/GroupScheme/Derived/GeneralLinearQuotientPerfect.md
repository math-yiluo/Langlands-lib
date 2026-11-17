# Perfectness of quotients of GL by the centre

This internal helper assumes that every determinant-one point of the actual
general linear group lies in its full derived subgroup, and proves that every
fppf quotient by its scheme-theoretic centre is perfect. This implication holds
over every field and for every finite index type. Together with the derived-group identification, it gives the third clause of the unchanged
`GeneralLinearCenterDerivedStatement` without any finiteness assumption on
the quotient. Its source provenance is inherited from Milne, *Algebraic
Groups* (2017), Examples 6.22 and 12.47, as documented in that statement pair.

The argument first treats a point over an affine test scheme. For positive
rank, the published `UnitPowerExtension.exists_roots_test` supplies a flat,
surjective, locally finitely presented refinement on which the determinant
has a root of order equal to the rank. The corresponding scalar point has
the same determinant, so dividing the restricted point by it produces an SL
point. The explicit determinant-one premise places this point in the full derived
subgroup of GL, and functoriality carries its image into the
full derived subgroup of the target. The scalar factor is killed because
it is central and the full centre lies in the kernel. Membership in each
closed commutator-containing subgroup descends along the refinement.
For empty index type the original point is the identity.

For an arbitrary test scheme the same result follows on its affine open
cover and glues using monicity of the closed subgroup inclusions. Finally,
for any quotient point, base change of the fppf quotient map provides an
fppf refinement with a GL lift. Its image lies in every closed
commutator-containing subgroup by the preceding argument; effective
epimorphism descent gives the same membership for the original point.
The proof uses the full kernel identity of the quotient and never assumes
surjectivity on the points of an unrefined test scheme.
