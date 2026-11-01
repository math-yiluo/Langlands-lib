# Scalarization through normed product coordinates

This internal helper is part of the proposed proof of smooth scalar orbit
coefficients. It does not yet assert the archimedean orbit-coefficient theorem.

`continuousLinearMap_product_factors` proves that every continuous real linear
map from an arbitrary product of real normed spaces into a real normed space
factors through a finite subproduct. Continuity bounds the output norm by a
finite supremum of coordinate norm seminorms. The map therefore vanishes on
vectors whose selected coordinates are zero. Extending the selected coordinates
by zero supplies the finite-subproduct map and the exact factorization.

`contDiffOn_comp_product_of_coordinates` uses that factorization: a parameter
family smooth in every normed coordinate remains smooth after applying the
continuous linear map. The proof applies the finite-product smoothness theorem
and composition with a continuous linear map. It does not assume a norm or a
smoothness structure on the entire infinite product.

`continuousLinearMap_extends_product_embedding` transports a map with
finite-dimensional target to the range of a linear topological embedding,
then applies the locally convex Hahn–Banach extension theorem.
`contDiffOn_scalar_of_product_embedding` combines this extension with finite
coordinate factorization. Smoothness of all normed coordinates therefore gives
smoothness after the original continuous linear map.

These are internally derived lemmas using Mathlib's seminorm continuity and
finite-product calculus. No external mathematical result is attributed beyond
those imported dependencies. Connecting the actual derivative compact-open
topology to normed compact-restriction coordinates, and proving smoothness of
the actual parameter families in those coordinates, remain separate steps.
# Directional derivative identification

`fderiv_scalar_of_product_embedding_apply` uses the same extension and finite
coordinate factorization to identify a scalar derivative. If every normed
coordinate is differentiable at the parameter and its derivative in one
direction equals the coordinate of a specified vector in the source, the
scalar derivative equals the functional applied to that vector. This statement
requires no normed structure on the embedded source and introduces no
differential calculus on it.
