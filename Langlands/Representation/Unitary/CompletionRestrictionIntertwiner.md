# Completed intertwiners into a restricted representation

This internal construction specializes the published positive-form completion
machinery to an intertwiner whose target action is restricted along a group
homomorphism. The source and target groups and both complex module carriers
have independent universes. No topology on those original groups or carriers
is required.

Let `b` be an invariant positive form for a representation `ρ` of `H` on `V`,
and `c` one for a representation `σ` of `G` on `W`. Let `φ : H →* G` and
`f : ρ.IntertwiningMap (σ.comp φ)` preserve the two forms. These are supplied
inputs. Restriction copies the positive core, so `(c.comp φ).HilbertCompletion`
and its canonical original-vector map are those of `c`.

`completedIsometry_comp_completedOperator` proves covariance of the actual
completed isometry with the source operator at `h` and the original target
operator at `φ h`. It composes the published completed-isometry covariance
with `comp_completedOperator`. `completedEquiv_comp_completedOperator` records
the same formula when the original intertwiner is surjective, for the actual
completed isometric equivalence. The same-group helper
`completedEquiv_completedOperator` records the underlying equivalence formula
without restriction.

`completedIntertwinerAlong` packages that isometry as an intertwiner from
`b.completedRepresentation` to `c.completedRepresentation.comp φ` on the same
actual Hilbert carriers. Its application agrees definitionally with the
completed isometry, and continuity follows from its isometric construction.
`completedRangeAlong` is its actual invariant range. Its underlying submodule
is exactly the linear-map range of that isometry; its underlying set is the
function range. Completeness of the source makes this image closed. Finally,
`coe_completedRangeAlong_eq_closure` identifies it with the closure of
`v ↦ c.toHilbert (f v)` in the target completion by the published generic
completed-range closure theorem.

The provenance is entirely internal: `Restriction.comp`,
`CompletionIntertwiner.completedIsometry` and its covariance and closed-image
laws, `CompletionTransport.completedEquiv`, and the restriction identity in
`CompletionOperations` supply the construction and all its obligations.
No positive-form existence, target surjectivity in the nonsurjective case,
continuity in the group variable, or decomposition theorem is asserted.
