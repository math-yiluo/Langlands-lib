# Additive equivalences of modules over the lifted integers

`Langlands.LinearAlgebra.liftedIntLinearEquivOfAddEquiv` turns any supplied
additive equivalence `M ≃+ N` into a linear equivalence over `ULift.{u} ℤ`,
using the supplied module structures on both additive commutative groups.
The scalar universe `u` and the carrier universes `v`, `w` are independent.

This is an internal derived construction. Every lifted integer is the
integer cast of its underlying value. For each supplied module structure,
`Int.cast_smul_eq_zsmul` identifies multiplication by that scalar with
integer multiplication in the underlying additive group. Additive
homomorphisms preserve integer multiplication by `map_zsmul`; this proves
the required scalar law. The underlying additive equivalence, including
its inverse and both inverse laws, is retained exactly.

The construction is useful when two legitimate module structures over the
lifted integers have the same integer action but differ as Lean instance
terms. It preserves both actual module structures instead of assuming
they are definitionally equal. In the integral Chevalley classification
proof, it connects the actual root-weight module structure from the
generic PID theorem with the lifted-integer action inferred by the
unchanged integer-specific statement. No torus splitting or group
classification assertion is made by this module.
