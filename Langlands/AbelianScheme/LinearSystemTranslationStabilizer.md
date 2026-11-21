# Generic vanishing and the translation stabilizer of a complete linear system

`CompleteGeneratingSystem.overMap` regards the actual projective map of a complete
basis without common zeros as an arrow over the field. Its underlying map is the
original linear-system map of the basis.

Let `A` be an abelian scheme over an algebraically closed field and `N` a line
bundle. If for every rational point some section of `N` is nonzero there,
`exists_completeGeneratingSystem_abelian` supplies a complete generating basis.
The proof uses finiteness of coherent cohomology on the proper scheme, the
comparison of degree-zero cohomology with global sections, and generation from
rational points. It does not require ampleness at this step.

For any such basis, suppose that for all rational `y` in a nonempty open of `A`,
vanishing at `y` implies vanishing at `a · y` for every global section, for a fixed
rational point `a`. The pencil criterion for the basis gives equal images of
`y` and `a · y`. Smoothness provides reducedness; smoothness, properness and
geometric connectedness give irreducibility. Thus the open is dense and the
rational-slice test puts `a` in the stabilizer of the map, using commutativity
to compare the two orders of multiplication
(`mem_linearSystem_stabilizer_of_generic_translation`).

The tangent version takes a dual-number point `t` reducing to the unit. Its
translate by `y` reduces to `y`. If every section vanishing at `y` vanishes on
that translate, the dual-number pencil test compares the actual translated
map with the constant lift at `y`, including their nilpotent coefficients.
The rational-slice test applies with the dual-number parameter scheme, so
`t` belongs to the same stabilizer on that test scheme
(`mem_linearSystem_stabilizer_of_generic_tangent`).

`ampleGenericVanishings_of_trivial_linearSystem_stabilizers` assumes that for
every complete generating basis of an ample bundle in this setting the
translation stabilizer functor is trivial. It derives the two generic vanishing
statements: the rational translation must be the unit, and the putative nonzero
tangent would equal the constant lift at the unit. The stabilizer-triviality
premise is not proved in this module.

These are internal adapters between the Library's actual linear-system maps,
pencil tests and translation stabilizer functors. They implement the common
part of the point and tangent branches of cubic separation without replacing
nilpotent test schemes by their underlying points.
