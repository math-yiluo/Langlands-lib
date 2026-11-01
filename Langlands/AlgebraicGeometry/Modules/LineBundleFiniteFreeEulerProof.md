# Finite free factors in line-bundle Euler characteristics

`lineBundleFiniteFreeEuler` proves the complete
`LineBundleFiniteFreeEulerStatement`. The helper
`lineBundleFiniteFreeTensorIso` uses the proved tensor invertibility of the
actual line bundle and `tensorInvertibilityEquivalence` to make tensoring on
the left an equivalence. The localized monoidal tensor comparison returns
to the explicit sheaf tensor in the target. Reindexing the free sheaf's
coproduct from `ULift (Fin r)` to `Fin r`, preservation of coproducts by
the equivalence, and the right unit isomorphism give the finite coproduct
of `r` copies of the line bundle.

`finiteCoproductCohomologyIso` first proves additivity of actual relative
cohomology. For maps `f` and `g`, the sum of their chosen descents between
injective resolutions is a descent of `f + g`. The published
`Functor.rightDerived_map_eq` computes the three derived maps with these
descents. Additivity of the original functor on complexes, of homology,
and of composition then gives additivity of the derived functor.
This preserves the finite coproduct, which is identified with the biproduct
and then with the ordinary finite product of vector spaces.
`lineBundleFiniteFreeCohomologyIso` composes the tensor and cohomology
comparisons.

Every original cohomology vector space is finite dimensional, so its finite
product is finite dimensional. Beyond the original vanishing cutoff these
products are subsingletons, hence zero objects. This proves finite cohomology
for the tensor with the free sheaf, including the empty product at rank zero.
The product dimension formula gives `r` times the original cohomology
dimension in each degree. Multiplication commutes with the integer finsum;
the alternating dimension formula then gives the stated Euler identity for
any finiteness witness.

This proof is an internal derivation from the published actual sheaf,
tensor-invertibility and cohomology constructions and Mathlib's finite
coproduct and vector-space dimension results. It assumes no numerical rank
formula or Euler polynomial.

`finiteFreeSectionsIso` evaluates the actual free sheaf on any open. After
reindexing its finite coproduct from `ULift (Fin r)` to `Fin r`, the additive
evaluation functor preserves that coproduct. The finite biproduct and product
comparison identifies the resulting section module with `Fin r → Γ(X,U)`.
`finiteFreeSections_finite` transports its module finiteness, including rank zero.
`restrictFiniteFreeIso` uses coproduct preservation of the restriction left
adjoint and its structure-module isomorphism to identify the restriction with
the actual free sheaf of the same rank. These are internal helper comparisons
for applying coherent Euler-sequence results on a generic free chart.
