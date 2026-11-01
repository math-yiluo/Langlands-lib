# Actual adelic block unipotent radicals

Author: Worker 2.

This internal construction uses the actual kernels and Levi factorization in
`Group/GL/Blocks` and the actual coefficient maps in
`Global/AdelicBlockParabolic`. The number field `F : Type uF` has arbitrary
universe. The rank is any natural number, with an ordered positive block shape
`B : BlockShape n`, including the empty shape in rank zero.

`Rational`, `Full`, `Finite` and `Infinite` are the existing block upper
unipotent radicals over `F`, the full adele ring, its finite restricted-product
factor and its archimedean completion product. Each radical is the kernel of
the actual diagonal-block Levi projection inside the actual parabolic group.
Thus its diagonal blocks are identities and its blocks below the diagonal
vanish. The adelic topologies are the inherited subgroup topologies, including
the topology of both a matrix and its inverse. No topology on `F` is selected.

`rational` restricts the entrywise rational diagonal map. Its membership proof
uses the published identity-diagonal-block criterion and the preservation of
zero and one by the actual algebra map. `rational_injective` follows from the
proved rational parabolic injection.

`infinite` and `finite` restrict the genuine continuous parabolic projections.
Their kernel membership follows from the proved compatibility with the Levi
projection. `pair` pairs the actual parabolic matrices and their inverses;
compatibility with Levi projection and the two identity Levi components proves
kernel membership. The three inverse identities give `split`, a multiplicative
homeomorphism from the full radical to the product of the archimedean and finite
radicals. Continuity restricts the actual parabolic maps to their kernels.
`ofInfinite` and `ofFinite` include one factor with identity in the other.
`split_val` records compatibility with inclusion into the parabolic.

`infinite_leviAction` and `finite_leviAction` intertwine the actual Levi
conjugation actions using the respective coefficient maps on the Levi product.
Both proofs expand conjugation as `m*u*m⁻¹` inside the actual parabolic, then use
the homomorphism laws and the established compatibility of the block diagonal
section. `split_leviAction` assembles these two equations into the commuting
action diagram for the radical and Levi multiplicative homeomorphisms.

`infinite_unipotentPart` and `finite_unipotentPart` prove that removing the
actual Levi part, by `g*section(leviProjection(g))⁻¹`, commutes with coefficient
projection. The proofs use the same section compatibility and the published
Levi projection equations. `decomposition_infinite` and `decomposition_finite`
combine these identities with Levi compatibility: the two coordinates of the
existing unique `u*m` factorization commute with the actual projections.
The generic factorization and its homeomorphism remain the published
`B.decomposition` and `B.decompositionHomeomorph`.

Provenance is internal. This module restricts the already constructed
parabolic splitting to the already constructed diagonal-block kernel.
The action and factorization identities follow from the same actual maps,
the published block diagonal section and the group homomorphism laws.
There is no new identification with original literature. Haar measure on the
radical, modulus formulas, rational quotient compactness, normalized global
induction, isobaric representations and automorphic existence are separate
obligations.
