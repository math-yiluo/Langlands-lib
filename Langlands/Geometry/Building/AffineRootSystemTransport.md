# Affine root system axioms under affine equivalences

This is an internal, derived construction on the existing
`AffineRootSystem.IsAffineRootSystemWithRankZero` predicate. It extends the
functional, coroot and Weyl-group transport in `AffineWeylTransport` to all
seven fields of that predicate. It asserts no existence of an affine comparison
between apartments attached to different groups and adds no literature claim.

Let `A` and `B` be real affine spaces with translation modules `V` and `W`.
The four type universes are independent. For an affine equivalence
`e : A ≃ᵃ[ℝ] B`, the existing `affineFunctionalTransport e` sends an affine
functional `ψ` to `ψ ∘ e⁻¹`; `transportedRoots e Ψ` is the image of the actual
set `Ψ` under that equivalence.

The definition `derivativeTransport e` is the dual equivalence induced by
`e.linear.symm`, so the derivative of `ψ ∘ e⁻¹` is the image of `ψ.linear`.
The first lemmas prove this derivative identity, preservation and reflection
of derivative equality, and the identity of the entire derivative root set
with its image under this dual equivalence.

`derivativeFiber_transportedRoots` identifies each fiber over the derivative
of a root with the image of its original fiber under functional transport.
`boundedDerivativeFiber_transportedRoots` also identifies the subset whose
pointwise difference from a fixed root has absolute value at most `M`
everywhere on the apartment. The forward proof evaluates at `e x` and cancels
the inverse; the reverse proof evaluates the original bound at `e.symm y`.
Thus the universal bounds have exactly the meaning in the original predicate.

`IsAffineRootSystemWithRankZero.transport` proves every field of the existing
predicate for `transportedRoots e Ψ`:

- The derivative roots span the whole dual module because linear equivalences
  take spans to spans and are surjective.
- Their derivatives are nonzero because the dual equivalence is injective.
- The derivative root set is finite because it is the image of a finite set.
- A coroot `v` transports to `e.linear v`, using the existing
  `isCoroot_transport_iff`.
- Integral pairings transport by pulling an arbitrary target coroot vector
  back through the surjective linear equivalence and using the unchanged
  derivative pairing.
- Each derivative fiber is infinite because functional transport is injective.
- Each bounded derivative fiber is finite because it is an image of the
  corresponding finite subset.

Finally, inverse transport cancels on affine functionals, by evaluating at a
point and using the inverse law for `e`. It therefore cancels on root sets.
The entry definition `affineRootSystemTransportEquiv` packages forward and
inverse transport as an equivalence between the subtypes of actual root sets
satisfying `IsAffineRootSystemWithRankZero` on `A` and on `B`. Its inverse uses
`e.symm`, and subtype equality reduces the two inverse laws to root-set
cancellation.

No topology, nonempty-root-set assumption, finite-dimensionality, or building
data is required. The rank-zero convention is exactly the imported predicate;
this construction does not replace it with the separate affine-spanning
predicate in `AffineRootSystem`.
