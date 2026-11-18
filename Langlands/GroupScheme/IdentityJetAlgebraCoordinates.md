# Algebra comparisons for actual identity jet sections

The map on sections induced by the actual projection of an identity jet
gives its section ring a `Γ(S,U)`-algebra structure. `jetSectionAlgebra`
exposes this structure for an arbitrary base open `U`. Scalar
multiplication is the action on sections of the pushed-forward actual
structure module.

Suppose `S` carries a group scheme `G`, `G` has an ambient coordinate map
to `Spec B`, and the ring `A = Γ(S,U)` and coordinate algebra `B` are
`R`-algebras. Given a linear equivalence from `A ⊗_R (B/I)` to the actual
jet module sections over `U`, `algEquivOfJetCoordinateFormula` upgrades it
to an `A`-algebra equivalence if `a ⊗ [c]` maps to `a` times the actual
jet restriction of the ambient coordinate `c`. The ring map giving this
restriction preserves products and one. Taking quotient representatives
reduces the test on pure tensors to these ring identities, and the
tensor-product criterion extends multiplicativity to every element. The
underlying linear equivalence and the pure-tensor formula are retained.

`baseChangeJetAlgEquiv` applies the criterion to the actual base-change
jet section comparison for an affine group over `Spec R`. The existing
pure-tensor formula uses restrictions of the global jet coordinates.
Restriction gives the corresponding actual function above `U`. The
algebra comparison has the original linear equivalence and this exact
formula on every `a ⊗ [c]`.

This is an internal consequence of actual scheme function pullback and
Mathlib's algebra tensor product. In the parabolic determinant proof,
the algebra comparisons allow the prescribed jet coordinates to be
evaluated at the actual universal jet point. The original subgroup and
its conjugate can then be compared using the same ambient coordinates.
