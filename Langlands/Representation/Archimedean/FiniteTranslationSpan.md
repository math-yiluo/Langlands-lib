# Finite spans under left and right translation

`FiniteTranslationSpanStatement` says that a complex-valued function on a group whose right translates have finite-dimensional span also has finite-dimensional span under simultaneous left and right translation.

Let `V` be the right translate span of the function. Right translation preserves `V`. For each basis vector `vᵢ` of `V`, its matrix coefficients form the image of the finite-dimensional dual of `V` under the map that sends `ℓ` to `k ↦ ℓ(ρ(k)vᵢ)`. The sum of these finitely many images is finite-dimensional. Expanding a right translate of the original function in the basis of `V` and applying a point evaluation after `ρ(k)` expresses every two-sided translate in this sum.

`coefficient_mem` also proves that the matrix coefficient of a vector in a finite-dimensional function space stable under both translations belongs to that space. Point evaluations span the dual by annihilator duality, since a function vanishing at every point is zero. The coefficient evaluated against a point evaluation is a left translate, and taking linear combinations gives the conclusion.

This internal linear algebra supplies a finite-dimensional compact-profile space for the Godement continuation. Its two-sided translate span contains the given profile and can contain the values of compact-equivariant constructions on that profile for all parameter tuples.
