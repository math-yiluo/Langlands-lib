# Local coefficient splittings of permutation descent

This internal derived module recovers the actual splitting of the descended
invariant coefficient algebra on every affine chart, with its tensor formula.

`leftTensorEquiv` distributes the finite product in the left tensor factor while
retaining its product-base algebra action. `localDescentHom` is scalar extension
of invariant coefficients projected to one chart. `localDescentHom_component`
identifies its product with the global descent map. The global descent equivalence is conjugated by this left-product tensor
equivalence. Its bijectivity and componentwise zero-preserving maps give component bijectivity, hence the actual
`localDescentEquiv`. Its pure-tensor formula is multiplication of the chart
scalar with the invariant coefficient's chart value.

`invariant_overlap` applies actual overlap tensor coordinates to the defining
invariant coaction equation, giving equality of the two chart coefficient
families under the actual overlap transition.

The universe is arbitrary. Affine charts are a finite flat jointly surjective
family, coordinate types are finite with variable or zero rank, and rings may be
zero. No final Weil group comparison is asserted by this module.
