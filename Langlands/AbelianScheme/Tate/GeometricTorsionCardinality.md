# Actual torsion points and the actual kernel coordinate algebra

This internal comparison specializes the finite étale section-cardinality bridge to the multiplication kernel of an actual bundled abelian scheme over a separably closed field. `torsionCoordinates B n` is the ring of global functions on that actual kernel. Its scalar structure `torsionCoordinatesAlgebra B n` is induced by the actual kernel's structure morphism.

`torsionSectionsEquiv` identifies actual scheme sections of the kernel with the existing `GroupScheme.Tate.Level`, using the over-category section equation and the published `kernelLevelEquiv`. There is no replacement torsion module. `natCard_level_eq_finrank` uses the published finiteness and étaleness of the multiplication kernel when the integer is nonzero in the base field, then applies the generic cardinality bridge.

The result does not compute this dimension. In particular, the numerical formula `n^(2*g)` still requires its geometric proof. No hypothesis asserting that numerical formula or a torsion basis is included or discharged here.
