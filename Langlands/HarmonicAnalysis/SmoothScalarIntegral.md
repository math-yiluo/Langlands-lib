# Scalar integration as an algebraic functional

Author: Worker 1564.

This internal construction complements `SmoothWeakIntegral`. The measurable
integration space, topological group, and representation carrier have
independent universes. The carrier is an algebraic complex vector space;
no topology or norm on it is used.

`scalarIntegralFunctional` maps a smooth functional to the genuine complex
integral of its evaluation on the supplied vector-valued function. Its
hypothesis requires every such scalar function to be integrable. Scalar
integration is then additive and complex homogeneous, so the construction is
an element of the algebraic dual of `SmoothDual`. The evaluation lemma is
definitional.

`smoothScalarIntegralFunctional` additionally assumes one open subgroup under
whose actual smooth-contragredient action all these integrals are invariant.
The inverse-transpose action on the algebraic double dual fixes the integral
functional: invariance applied to the inverse subgroup element proves this
directly. Thus the construction lies in the actual smooth bidual. This
invariance is an explicit, checkable hypothesis, not a consequence of scalar
integrability alone.

`integrable_of_scalar_integrable_of_invariant` assumes admissibility of the
representation and compact-open cofinality for the supplied group topology.
The published `smoothBidual_surjective_of_compact_cofinal` gives a vector of
the original carrier whose smooth-bidual evaluation is this integral
functional. Evaluating that equality at each smooth functional gives the
original scalar integral equations. Together with the scalar integrability
hypothesis these are exactly `SmoothWeakIntegral.HasIntegral`, hence the
existing vector-valued weak-integrability predicate.

The provenance is internal: the proof composes the published admissible
smooth-bidual theorem with scalar Bochner-integral linearity. It asserts no
automatic smoothness of an arbitrary scalar-integral functional and proves no
analytic convergence estimate. The intended standard-intertwining application
must prove its open-subgroup invariance using the actual quotient measure and
induced representation.
