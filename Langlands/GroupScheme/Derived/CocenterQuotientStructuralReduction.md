# Cocenter existence from maximal-torus products and intersections

Authors: Worker 1616, with the integral cocharacter construction by Worker 1435.

This internal conditional assembly proves the exact proposition
`CocenterQuotientExistenceStatement` from two structural inputs:
surjectivity of multiplication of an actual derived subgroup and a supplied
maximal torus, and the torus property of their actual intersection. Both
inputs retain arbitrary fields and the arbitrary universe `u`.

`cocenterQuotientDataOfStructuralInputs` chooses an actual commutative
quotient group scheme and its projection under those inputs. The returned
dependent pair retains every conjunct of the cocenter proposition:
affineness, the exact fppf kernel, the torus property, and splitness and
integral cocharacter surjectivity over every field splitting each supplied
maximal torus. It uses classical choice on the proved conditional existence
theorem and makes no uniqueness claim about the chosen quotient.

The proof chooses `cocenterTorusQuotientData`, obtaining a smooth affine
commutative fppf quotient torus `Q`. Each maximal torus maps surjectively to
`Q`, and `Q` splits after any field extension splitting that maximal torus.
It remains to prove the integral cocharacter conclusion.

`IsTorus.epi_of_surjective_hom` turns the actual scheme surjection into a
group-scheme epimorphism. Smoothness of the target torus gives reducedness
and local noetherianity. The source torus gives local finite type and
quasi-compactness. Dominant homomorphism flatness makes the surjection
fpqc; its scheme epimorphism induces the required epimorphism of groups.

The actual restricted kernel is identified with the intersection using
`isTorus_kernel_comp_baseChange_of_isTorus_intersection`. The supplied
intersection property therefore makes the full kernel a torus after every
field extension, hence smooth and connected. Worker 1435's
`IsSplitTorus.cocharacter_surjective_of_smooth_connected_kernel` applies to
the resulting epimorphism of split tori and proves integral surjectivity
on the exact cocharacter lattices appearing in the target.

No structural input is discharged by this assembly. In particular,
scheme surjectivity alone is not used to infer integral cocharacter
surjectivity; smoothness and connectedness of the full kernel are explicit
consequences of the supplied intersection theorem.
