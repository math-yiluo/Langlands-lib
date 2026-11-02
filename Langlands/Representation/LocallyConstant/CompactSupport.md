# Compactly supported locally constant smooth modules

This internal construction uses the actual compact topological support of a
locally constant function. It extends the published compact-domain diagonal
construction to continuous group actions on possibly noncompact spaces.

The parameters have independent universes: a commutative coefficient ring, a
topological group, a space with a jointly continuous group action, and an
arbitrary coefficient module. Smoothness of coefficients is required only for
the smooth representation constructions. Coefficients carry no topology.
Neither local compactness nor separation nor compactness of the ambient space is
assumed. Empty domains and zero modules are included. With universes `uR`,
`uG`, `uX`, and `uV` for the ring, group, space, and coefficient carrier,
respectively, the constructed function module has universe `max uX uV`.
The smooth pullback morphism uses domain and target spaces in the same
space universe; the algebraic intertwiner allows independent space universes.

The spatial stabilizer is the subgroup fixing the whole function under
precomposition. Compactness of its topological support makes local constancy
uniform near the group identity on that support. Intersecting the resulting
neighborhood with its inverse also controls points outside the support: if a
zero value moved to a nonzero value, applying the inverse element at that new
support point gives a contradiction. This proves the actual global spatial
stabilizer open.

`submodule` is the entire submodule of `LocallyConstant X V` with compact
topological support, and `Functions` is its carrier. `range_finite` follows by
temporarily equipping coefficients with the discrete topology and using
compactness of the image of the support, together with the possible zero value.
No stabilizer condition is part of this carrier.

`representation` restricts the published diagonal representation:

```text
(g · f)(x) = ρ(g)(f(g⁻¹ · x)).
```

Translation is a homeomorphism and a linear coefficient operator sends zero to
zero, so this action preserves compact support. `inclusion` is the original
submodule inclusion into all locally constant functions. Coefficient
intertwiners act by pointwise postcomposition and preserve support.

For smooth coefficients, `commonOpenStabilizer` intersects the constructed open
spatial stabilizer with the finitely many open stabilizers of the coefficient
values. Its elements fix the entire function for the diagonal action.
`representation_isSmooth` therefore proves smoothness of the whole compact
support module, and `smoothRepresentation` bundles it as a `SmoothRep`.
`coefficientFunctor` retains every smooth coefficient morphism and acts
pointwise on values.

`pullbackIntertwiner` and `smoothPullback` use an original continuous equivariant
map with an explicit properness hypothesis. The topological support of a
pullback lies in the inverse image of the original topological support.
Properness makes that inverse image compact, and the pullback support is closed.
The underlying linear map is ordinary precomposition. No pullback on all
continuous equivariant maps is asserted.

This is derived infrastructure for supported smooth sections. It does not
construct a sheaf compact-support functor, derived cohomology, an analytic or
étale comparison, arithmetic coefficients, or the Harris specialization.
