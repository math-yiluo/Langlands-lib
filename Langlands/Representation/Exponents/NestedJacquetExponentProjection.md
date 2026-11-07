# Projection of actual fine Jacquet exponents to an outer parabolic

This derived internal module supports the converse direction of Renard VII.2.4.
It retains actual fine and outer parabolic, Levi and radical triples, an actual
inner parabolic of the original outer Levi with the same common Levi, rational
point nesting and intersection, and the common-Levi composite equality. The
geometric field universe and representation carrier universe are independent.

`fineToNestedLeviJacquetMap` is the forward actual normalized-transitivity map
from the fine Jacquet module to the outer-then-inner Jacquet module. It is
injective because it is the component of an existing natural isomorphism.
A nonzero uniform generalized eigenvector therefore gives the same exponent
in the iterated module, on the unchanged common-Levi split component.

For a tempered source, the outer Jacquet module is admissible by the existing
presentation and contraction argument. Given any compatible point factor
from its split component into the fine split component, the existing central
Jacquet exponent restriction theorem applies to this admissible outer module.
The resulting group exponent is exactly a normalized exponent of the original
outer Jacquet module. No extra Jacquet admissibility premise is assumed.

The proof uses normalized transitivity and central restriction already proved
in the Library; it does not construct an outer parabolic, assume a new analytic
criterion, or prove the full square-integrability equivalence.

For a genuine scheme morphism between the original split components, the
composite identity supplies the required point compatibility directly. If the
normalized real part of the fine exponent restricts to zero along that map,
functoriality of the normalized real part makes its projected outer exponent
unitary. The existing characterization of unitary-part vanishing then proves
that the original outer unitary Jacquet part is nonzero. The map and composite
identity remain supplied; this result does not assert existence of a coarser
parabolic or a boundary-face realization.
