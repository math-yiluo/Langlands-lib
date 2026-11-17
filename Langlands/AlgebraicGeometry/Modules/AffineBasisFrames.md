# Free sheaf frames from bases on affine subopens

This internal unit constructs an actual free sheaf frame from a finite
family of sections. Let `M` be a module sheaf on an arbitrary scheme `X`,
let `U` be an open, and let `m : I → Γ(M,U)` have a finite index type `I`.
Assume that on every affine open `V ≤ U`, the restricted family is the
underlying family of a basis of `Γ(M,V)` over `Γ(X,V)`. No quasi-coherence
assumption is required.

`sectionOver` forms the compatible restriction family of an actual section.
`basisSectionsHom` is the actual morphism from the free sheaf on the slice
site of `U` to `M.over U` given by these sections, using the free-sheaf
universal property. `basisSectionsHom_freeSection` computes it on every
canonical free generator.

The auxiliary `freeOverSectionBasis` supplies the canonical finite basis
of sections of the free sheaf on every object of the slice site. Its
coordinate functionals are the canonical free-coordinate morphisms. The
sum of coordinate projection followed by free inclusion is the identity,
which proves the expansion formula and the coordinate equivalence.

`isIso_of_bijective_affineOver` is a local criterion for an arbitrary
morphism of module sheaves on that slice site. Bijectivity on all affine
subopens makes its image and equalizer sieves covering: every point of
every open has an affine neighborhood inside it. Local bijectivity of the
underlying sheaf map then proves it is an isomorphism, which the forgetful
functor from module sheaves reflects.

The basis hypothesis identifies the section map of `basisSectionsHom` on
each affine subopen with the linear equivalence between the canonical
free basis and the supplied target basis. The local criterion proves
`isIso_basisSectionsHom`, and `affineBasisFrame` is the resulting actual
isomorphism from the free sheaf to `M.over U`. The theorem
`affineBasisFrame_basis` identifies its basis on every smaller open,
including nonaffine opens, with actual restrictions of `m`.

The provenance is internal sheaf and linear algebra. The construction uses
the existing actual free sheaf, its section universal property, affine-open
neighborhoods and the local bijectivity criterion. It asserts no geometric
positivity.
