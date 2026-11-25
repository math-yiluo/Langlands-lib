# Two-factor descent using a smooth integral intersection model

This internal derived helper uses `unramifiedIntegralCosetDescent`. It concerns
actual coefficient points of group schemes, with `K = inertiaFixedField F`,
the maximal unramified extension.

For a morphism `q : U → G`, a supplied integral model `M` of `U`, and subgroups
`A` and `B` of `G(K)`, `M.IsIntersectionModel q A B` says that a point of `U(K)`
has integral model coordinates exactly when its image belongs to `A ∩ B`.
This definition includes an exact comparison on all `K`-points. It does not
construct a model.

The theorem `IntegralModel.exists_rational_factorization_of_intersectionModel`
assumes that `U` is affine and locally of finite type, that the supplied model
is smooth with connected special fibre, and that `A` and `B` are stable under
every coefficient automorphism of `K/F`. Given an actual rational point `g`
and a factorization `g_K = q(x)y` with `q(x) ∈ A` and `y ∈ B`, it constructs
actual rational points `u ∈ U(F)` and `v ∈ G(F)` with
`g = q(u)v`, `q(u)_K ∈ A`, and `v_K ∈ B`.

The proof uses rationality of `g` to calculate

```
q(x)⁻¹ σ(q(x)) = y σ(y)⁻¹.
```

The left side belongs to `A` by stability and the right side belongs to `B`.
Naturality of coefficient points identifies this element with the image of
`x⁻¹σ(x)`. The intersection comparison makes that discrepancy integral.
The published coset descent theorem then produces `u_K = xh` with `h`
integral. Its image lies in `A ∩ B`. Taking `v = q(u)⁻¹g` gives
`v_K = q(h)⁻¹y ∈ B`, while `q(u)_K = q(x)q(h) ∈ A`.
These calculations require no commutativity, injectivity of `q`, or reductivity.

The provenance is internal and source-free beyond the named published input.
The intended root-filtration application orders the central doubled-root
factor first and supplies its intersection depth model separately.
This helper neither constructs that model nor proves its comparison with a
supplied apartment valuation, and it does not assert a full unramified root
comparison field.
