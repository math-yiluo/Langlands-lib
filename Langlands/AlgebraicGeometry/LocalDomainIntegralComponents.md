# Integral open components from domain stalks

This derived construction supplies the disconnected-scheme reduction for
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4. It needs
domain stalks, without using integral closedness.

`irreducibleComponent_eq_of_stalk_isDomain` proves that a point whose
stalk is a domain belongs to only one irreducible component. The spectrum
of that stalk is irreducible. The generic points of any two components
through the point lift to its spectrum; the image of the latter's
generic point specializes to both. A component's generic point has no
proper generization, so the two generic points, and hence the two
components, coincide. Thus all irreducible components are pairwise
disjoint when every stalk is a domain.

In a noetherian topological space there are finitely many irreducible
components. The complement of one component is the finite union of
the others, so `isOpen_irreducibleComponent_of_stalk_isDomain` proves
that each component is open.
`integralComponentOpen` constructs the corresponding actual open, and
`isIntegral_integralComponentOpen` proves that its scheme is integral.
Reducedness follows from the domain-stalk hypothesis, and irreducibility
from its underlying irreducible component.

`affineNeighbourhoodOfIntegralComponentOpens` takes an affine
neighbourhood of the inverse image of `E` in each component and returns
an actual affine open of the whole scheme containing `E`. The images
are pairwise disjoint affine opens; their finite union is affine.
The empty scheme and empty component index are included. All
declarations apply in every universe.
