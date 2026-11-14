# Naturality of the torus inertia comparison

This internal helper derives naturality of the selected comparison
`π₁(T)_I → X_*(T)_I` for an actual morphism of tori over a field. It assumes the
Library's algebraic fundamental-group comparison and map statements, torus
fundamental comparison statement, fundamental inertia map statement, and torus
inertia comparison statement. It proves none of these assumptions unconditionally.

The proof uses surjectivity of the inertia coinvariant projection to choose a
representative. The defining projection laws for the selected inertia map and
both selected torus comparisons reduce the square to naturality of the torus
fundamental comparison. The latter is the conditional theorem in
`TorusInertiaFunctoriality`; its assumptions are retained here. The actual torus
inertia map has its projection law by construction.

The result is a formal consequence of the existing interfaces and the earlier
helper, with no additional literature assertion. It does not assert naturality
of the torus Kottwitz homomorphism.
