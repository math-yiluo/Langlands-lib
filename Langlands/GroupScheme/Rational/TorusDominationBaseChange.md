# Field extension of pointed torus domination

This internal construction transports an actual pointed dominant scheme
morphism from a torus through arbitrary extension of the ground field. It
applies to reduced affine targets, and hence to smooth affine targets that
already admit such a parametrization. No separability, algebraicity,
perfection, infinitude, or characteristic assumption is used.

For the actual pullback functor on over schemes, the proof constructs the
cartesian square associated with a morphism. A quasi-compact schematically
dominant morphism remains schematically dominant after flat base change.
Quasi-compactness is preserved by the same square, giving ordinary dominance
of the pulled-back morphism. A torus source and an affine target make the
original morphism quasi-compact. Reducedness of the target upgrades its
original topological dominance to schematic dominance.

Pointedness is preserved by applying the monoidal pullback functor to the
identity-section equation and precomposing with its monoidal unit morphism
`ε`. The transported identity section is precisely `ε` followed by the image
of the original identity section. This argument does not require the
parametrizing morphism to be a group homomorphism. The existing torus
base-change theorem supplies the torus property of the pulled-back source.

A dense image of a connected torus makes the target connected. For a smooth
affine target the published smooth connected group theorem consequently
supplies geometric integrality and reducedness, yielding the smooth version
of the base-change result without an extra connectedness assumption.

`HasPointedSplitTorusDomination` requires an actual pointed dominant morphism
from a split ground-field torus. Choosing the splitting extension already
contained in the original source's torus predicate and applying the same
pullback argument gives this stronger property over some field extension.
The result makes no claim that the chosen extension is finite or separable.
It does not assert splitness of a unipotent radical or maximal-torus
conjugacy. The provenance is an internal derivation from the existing torus,
flat base-change, and smooth connected group interfaces.
