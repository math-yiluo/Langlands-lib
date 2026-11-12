# Full specified-isomorphism tangent lifting for the finite basis family

This internal adapter derives its constructions and lemmas from the published
`FiniteBasisPicardFamily`, `ArtinianChartTestReduction`, and the generic
`PseudofunctorPointFiberIdentity` helper. It introduces no external source input
or unproved mathematical premise. All declarations retain the common arbitrary
universe `u`.

Let `k` be a commutative ring, `K` a field with its original `k`-algebra
structure, `f : X → Spec k` a morphism, and `M` an actual line bundle on the
residue fibre. The general lemma `hasLiftingForAt_of_parameters` applies to any
pointed deformation `D` on an augmented local Artinian test `A`. Its hypothesis
requires that every actual pointed dual-number deformation is isomorphic, in
the pointed deformation groupoid, to a restriction of `D` along some actual
augmentation-preserving map `A → K[ε]`. Its conclusion is the full
`ArtinianChartVersality.HasLiftingForAt` predicate for `D.right.of`, at the
specified augmentation point and along the dual-number augmentation. This
lemma does not require properness of `f`.

The proof first uses the identity-test reduction from
`ArtinianChartTestReduction.hasLiftingForAt_iff_base`. For an arbitrary actual
dual-number bundle and a compatible residue point, the residue test's identity
inclusion forces the chart map to equal the augmentation point of `A`. Compose
the original pointing arrow of `D` with the given residue isomorphism to equip
the dual-number bundle with its prescribed pointed deformation structure. The
hypothesis supplies a parameter map and a pointed isomorphism from the
restriction of `D` to that deformation.

The generic helper
`PseudofunctorPointFiber.exists_identityPoint_of_pointedIso` then turns this
pointed isomorphism into an actual point on the identity test. Its restriction
is exactly the originally specified residue point. The required epimorphism
hypothesis on the pointing arrow holds because the Picard fibre is a groupoid.
Thus the conclusion retains equality of the specified isomorphisms as well as
equality of the actual chart maps, on every compatible slice test.

When `f` is proper, `bundle` is the underlying actual line bundle of the finite
tangent-basis family. The final lemma `hasLiftingForAt` specializes the general
lemma to this family. The published
`FiniteBasisPicardFamily.existsUnique_parameter` supplies the required pointed
realizations using the weighted coefficient map. Only its existence assertion
is used. Neither the specialization nor the general lemma assumes that `K` is
finite as a set, or that a coefficient-field section of the augmentation exists.

This result concerns the initial finite tangent test. Transfer to the
complete-source tower and its effective bundle, and lifting for all Artinian
surjections, remain separate obligations.
