# Scalar Čech cochain isomorphisms and bounded flat terms

This internal module exposes the geometric and complex-theoretic ingredients
needed to apply bounded-flat scalar-extension results to actual alternating
Čech cochains. Schemes, rings and modules lie in an arbitrary common universe.

`scalarCechIntegerCochainMap` extends the specified scalar Čech cochain map
from natural to integer degrees, preceded by the isomorphism commuting
extension of scalars with extension by zero. For a Cartesian square and a
quasi-coherent coefficient, separatedness of the family over the affine base
makes this map invertible. The proof transports the existing isomorphism on
sections of the sheafified Čech complex through the sections-complex
isomorphisms, then applies the extension functor. The ring map is arbitrary.

`cechBaseChangeCochainMap_eq` identifies the previously specified map attached
to a chain map into line-bundle Čech cochains with scalar extension of that
chain map followed by `scalarCechIntegerCochainMap`. This is the defining
factorization, with the affine morphism instance supplied by Cartesianity.

The alternating Čech cochain module is zero above the cardinality of the
finite ordered cover. This follows from the existing empty-index argument in
`CechProjectiveTransport.subsingleton_cochain`. Transport through the
degreewise extension isomorphisms gives a strict upper bound for the
integer-extended complex. Its strict lower bound is zero.

For a flat separated family over the affine base and an actual line bundle,
every cochain term is flat over the base ring. The proof applies the published
`OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial`, converting the
line bundle's local restriction trivializations to pullback trivializations.
Terms of the integer extension are flat by the degreewise extension
isomorphisms; missing degrees are zero.

The provenance is internal specialization and transport of the imported
constructions and proved lemmas. The import containing the finite-cover
combinatorial helper does not impose a noetherian hypothesis on these
results. This module asserts no preservation of arbitrary quasi-isomorphisms
under scalar extension and no existence of a perfect model.
