# Integral lifts of actual reductive-quotient root points

This internal construction works at arbitrary universe over a Henselian local
domain with algebraically closed residue field and a specified fraction field.
It uses a supplied relative-component model, integral torus, split witness for
that torus, and actual reductive special-fibre quotient.

For each nonzero generic character `a`, every rational point of the quotient's
intrinsic root functor for `T.characterSpecialization hT a` lifts to an integral
section of the neutral model. Its generic point belongs to the original
intrinsic root group for `a`, and its reduction followed by the specified
quotient projection is the prescribed point. The construction `rootQuotientLift`
selects such a section and `rootQuotientLift_spec` retains both properties.

The proof takes the integral character corresponding to `a` through the given
torus. `IntegralModel.SplitRoot` supplies its smooth closed integral root model.
All-test root-functor base change identifies its special fibre with the
corresponding root functor of the neutral special fibre. The quotient projection
is smooth by `ReductiveQuotientRoots.projection_smooth`, so
`RelativeRoot.exists_root_point_lift_of_smooth` lifts the target root point
to this source root functor over the algebraically closed residue field.
Representability turns it into a point of the actual root model, and Henselian
reduction lifts it to an integral section. The generic torus square identifies
its generic root group, while reduction naturality gives the exact prescribed
quotient image.

This is a derived construction from the named Library interfaces. It makes no
claim about the kernel of the root projection, survival of any particular
character in the quotient, facet vanishing, or the final derivative root datum.
