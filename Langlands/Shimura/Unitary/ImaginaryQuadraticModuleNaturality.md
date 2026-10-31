# Semilinear naturality of the imaginary quadratic module decomposition

This internal extension of `ImaginaryQuadraticModule` treats a map between
arbitrary compatible coefficient `K`-algebras `f : R → R'`, together with an
actual `f`-semilinear map `F : M → M'` intertwining the given imaginary-field
actions. The imaginary quadratic CM number field `L`, its containing
characteristic-zero field `K`, and all compatible rational module and algebra
structures have the same meaning as in the preceding module. Both coefficient
rings and both module carriers have independent universes.

`factorCharacter_naturality` proves preservation of the natural or conjugate
scalar character using the coefficient map's preservation of `K`-scalars.
Tensor induction and semilinearity prove `tensorAction_naturality`: the given
map intertwines the induced tensor actions along the actual coefficient tensor
map. Applying this to the actual coordinate idempotent, whose preservation was
already proved, gives `moduleProjector_naturality`.

`map_mem_eigenmodule` proves that every vector satisfying all simultaneous
scalar eigen equations is carried to the corresponding eigensubmodule. It uses
the given intertwining equation, semilinearity and preservation of the selected
character. `eigenmoduleMap` is the resulting actual semilinear map between those
submodules, and its value is the original map on the included vectors.
`eigenmoduleEquiv_naturality` proves that applying the constructed product
decomposition after `F` equals applying the two induced maps to the constructed
decomposition before `F`. Restricting the identity gives the identity map.
`eigenmoduleMap_comp` proves that restriction of a composite is the composite
of the restrictions; the composite intertwines the actions by successively
applying the two input intertwining equations.

These are derived algebraic naturality results. No output eigensubmodule map,
projector comparison or naturality equation is assumed. There is no finiteness,
flatness or reducedness restriction on the coefficient rings or modules. This
unit does not construct sheaf restrictions or a sheaf tensor product and does
not yet assert a geometric or arbitrary scheme-base-change comparison.
