# Module-valued Hom complexes

Author: Worker 13.

Let `C` be an `R`-linear preadditive category, where `R` is a ring. For actual
integer-graded cochain complexes `P` and `Q`, `complex R P Q` is a cochain
complex of `R`-modules. Its degree `n` term consists of all families of
morphisms `P.X p ⟶ Q.X q` with `p + n = q`. These are products of actual
morphism modules, not finitely supported families. The implementation reuses
Mathlib's `CochainComplex.HomComplex.Cochain` and linear differential.

In degree `n` the differential is
`d(z) = d_Q ∘ z - (-1)^n z ∘ d_P`, with the indicated component shifts.
Mathlib writes categorical composition in traversal order and expresses
the second sign as `(-1)^(n+1)`. Its proved shape and square-zero identities
supply the intrinsic complex fields. No exactness or resolution is assumed.

`precompLinear` and `postcompLinear` are actual linear maps of graded
morphism modules. `map` combines them into a chain map, with commutation
proved using the differential identities for composition with a chain map.
`map_f_apply` gives the component formula `f_p ≫ z_p ≫ g_q`.
`map_id` and `map_comp` prove both functoriality laws. These construct a
covariant `functor`, the natural maps `precompose`, and the full `bifunctor`
contravariant in its first complex and covariant in its second.

`cohomology` applies Mathlib's actual homology functor in the abelian category
of modules. `precomposeCohomology` supplies its contravariant natural maps.
These are cohomology modules of the specified Hom complexes. They are not
called derived Ext without a separate resolution and comparison result.

The ring universe, category-object universe and category-morphism universe
are independent. The Hom complex takes values in modules in the
category-morphism universe. No abelian structure or enough-injectives
assumption is imposed on `C`.

## Provenance and use in the Harris construction

This is an internal categorical construction using the pinned Mathlib
implementation `Algebra/Homology/HomotopyCategory/HomComplex.lean`,
in particular `Cochain`, `δ_hom`, `δ_shape`, `δ_δ`, `δ_comp_ofHom` and
`δ_ofHom_comp`. Worker 13 inspected those definitions and proofs at Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`. The new construction
retains the coefficient-module structure and packages the two variances
and their cohomology maps.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed pp.305-306, equations (2.4)-(2.6),
constructs free resolutions and their total complexes. Printed p.309,
Proposition 4.4 and equation (4.4.1), specifies derived Hom in the category
of smooth coefficient representations. Worker 13 read these original pages.
The present construction is reusable input for applying Hom to actual
complexes in that category. It does not supply Harris's geometric complexes,
their projectivity or acyclicity, a totalization of his particular double
complex, a spectral sequence, or an identification with derived Ext.

Registered original: `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
