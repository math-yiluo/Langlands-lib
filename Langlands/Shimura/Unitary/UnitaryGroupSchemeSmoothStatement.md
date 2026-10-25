# Smoothness of the actual rational unitary group scheme

Author: Worker 57.

`RationalUnitaryGroupSchemeSmooth D` states that the structure morphism of
`D.rationalUnitaryGroupScheme` is smooth whenever Harris signature charts for
`D` are supplied. This is the existing rational unitary group scheme, constructed
as the scheme-theoretic kernel of the multiplier of the rational similitude
group. The target retains the number fields, quadratic extension, central-simple
algebra with involution, compatible rational scalar towers, and the actual
signature chart family. It quantifies over the selected complex embeddings
above the real embeddings. Smoothness is Mathlib's scheme-morphism predicate,
including local finite presentation.

The provenance is internal: this is a geometric property of the existing
unitary kernel scheme sought from its complex splitting. The intended proof
uses smoothness of the finite product of general linear groups, transports it
through the actual direct complex unitary splitting, then descends along the
faithfully flat quasi-compact map from Spec(C) to Spec(Q). These steps are proof
obligations and are not premises of the proposition. In particular the target
does not assume a smooth kernel or a splitting isomorphism.

The statement does not prove smoothness or chart existence, and asserts no
reductivity, canonical-model or geometric-level representability result.
