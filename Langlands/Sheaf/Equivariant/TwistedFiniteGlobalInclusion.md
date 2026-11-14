# The global-section inclusion under finite base subcovers

This derived internal construction packages the finite-cover descent in
`TwistedFiniteGlobalSections` for the actual smooth-global-section inclusion
of `TwistedExactGlobalComparison`.

Let a topological group `G` act on an object `X`, and let `P` contain identities.
For a module-valued sheaf on a topology of the twisted category, assume that
every covering sieve of the base contains a finite covering family and that
the sheaf is locally discrete for a system consisting of lifted local actions.
`isSmooth_baseSections_of_locallyDiscrete` proves that the representation of
`G` on all sections at the base is smooth. It applies the preceding
finite-cover descent theorem and interprets the resulting open fixing subgroup
of the top open subgroup as an open fixing subgroup of `G`.

Now suppose also that `P` respects isomorphisms and that the site over `X`
has a translation-invariant topology `J`. The canonical map
`sheafSmoothGlobalInclusion` sends a smooth vector to its underlying section.
For any sheaf satisfying the preceding assumptions, it is injective by
subtype injectivity and surjective because every section is smooth.
`isIso_sheafSmoothGlobalInclusion_app_of_locallyDiscrete` applies the
concrete module-category criterion to this bijection.

For any category with a functor `incl` to these module sheaves, if every image
sheaf is locally discrete for the specified lift system, the same conclusion
holds naturally on that category.
`isIso_exactGlobalInclusion_of_locallyDiscrete` assembles the component
isomorphisms, and `finiteGlobalSectionsIso` packages the existing
`exactGlobalInclusion` as a natural isomorphism. Its forward transformation
is the canonical inclusion already defined in the Library.

No abelian structure or exactness of `incl` is needed for this degree-zero
construction. The finite-cover and local-discreteness hypotheses remain
explicit. This module supplies no analytic finite-cover theorem, higher-degree
acyclicity theorem, or proof of Berkovich's derived comparison.
