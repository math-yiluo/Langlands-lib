# Smoothness of the rational Harris group scheme

Author: Worker 57.

`RationalGroupSchemeSmooth D` states that the structure morphism of the
already constructed rational unitary-similitude group `D.rationalGroupScheme`
is smooth whenever Harris signature charts for `D` are supplied. The proposition
quantifies over the chosen complex embeddings above the real embeddings and
the actual compatible charts. It retains the number fields, quadratic extension,
central-simple algebra with involution, and rational scalar towers of the
published construction. Smoothness is Mathlib's scheme-morphism predicate,
including local finite presentation.

The target concerns the actual rational scheme, not just its rational points.
The charts are existing algebraic input; no smoothness, descent conclusion or
output scheme is supplied as an assumption. The proposition does not assert
existence of the charts. It adds no CM-section or signature restriction beyond
those in `HarrisSignatureCharts`.

This is an internal geometric consequence sought for the published rational
model and complex splitting. The intended proof first proves smoothness of
the general linear factors and the multiplicative group, applies finite-product
closure, transfers through the actual complex group-scheme isomorphism, and
descends along the faithfully flat quasi-compact map from Spec(C) to Spec(Q).
The iterated real/complex pullback must be compared with direct base change.
These are proof obligations, not premises of the statement.

This statement alone provides no smoothness proof, reductivity theorem,
canonical Shimura model, or scheme of geometric levels.
