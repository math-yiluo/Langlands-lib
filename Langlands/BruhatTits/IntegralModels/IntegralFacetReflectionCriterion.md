# Detecting facet hyperplanes from integral actual reflections

This derived unit gives the converse to integral descent of actual facet
reflections. Its data are a supplied parahoric datum `P`, a supplied
maximal-unramified building `C`, an injective equivariant building map `e`,
an unramified zero datum `E`, a rational point `g`, an arbitrary apartment
subset `Fa`, and a component model `D` with the exact characterization

```
D.neutral.baseChangeUnramified.integralPoints =
  E.zeroPoints ∩ C.pointwiseFixer (e '' (P.translatedApartmentMap g '' Fa)).
```

All declarations have arbitrary universe `u`. No facet condition or smoothness
of `D` is required.

`conjugated_normalizer_mem_integralPoints_iff` applies to an actual normalizer
`n` in the simply connected image. Its conjugate by `g` belongs to the image of
the actual integral sections of `D.neutral` if and only if `n` fixes every
point of `Fa`. The reverse implication is the integral descent construction
from `UnramifiedFacetReflections`. For the forward implication, extend the
integral point to the maximal unramified field and apply the model's displayed
fixer characterization. Equivariance and injectivity of `e` recover the
original translated-building fixed points. Cancel the action of `g` and use
the published apartment injection to recover the apartment fixed points.

With `P.SatisfiesApartmentAxioms` and `P.HasRootReflections`, the theorem
`conjugated_reflection_mem_integralPoints_iff` specializes this equivalence to
the actual reflection from any supplied nonidentity root point `u` and actual
opposite factor pair `hp`. The apartment axioms put this reflection in the
simply connected image. Its published affine action is the reflection with
functional `P.reflectionFunctional a u`, and the fixed points of that
reflection are exactly the zero set of the functional. Therefore the
conjugated point is integral exactly when that functional vanishes on `Fa`.

`mem_facetDerivativeRoots_of_integral_reflection` additionally assumes that the
functional is an ordinary affine root. Its vanishing then gives membership of
the original character `a.val` in `facetDerivativeRoots P Fa`, directly by the
definition of that set.

`ordinaryFacetRootOfIntegralReflection` constructs an actual ordinary affine
root vanishing on `Fa` without that additional assumption. The actual
nonidentity root point supplies an extended affine root. Apartment axiom AS4
says that this functional or twice it is an ordinary affine root. Both have
the same zero set, so choosing one gives the stated subtype. The factor of
two is retained explicitly: this construction does not assert that `a.val`
itself is a facet derivative root in this general case.

The unit derives these results from `UnramifiedFacetReflections`, the actual
opposite-pair affine action, AS4, generic apartment injection, and the
fixed-point formula for affine reflections. It neither lifts quotient roots
to integral reflections nor identifies the roots surviving in a reductive
quotient. Those remain separate prerequisites of the host root-datum theorem.
