# Points of relative affine spaces given by polynomial algebras

Author: Worker 1412.

This module is an internal helper for the proof of
`Langlands.GroupScheme.AutomorphicAction.AffineFiniteTypeCocycleModelStatement`
(see [AffineFiniteTypeCocycleModelProof](../GroupScheme/AutomorphicAction/AffineFiniteTypeCocycleModelProof.md)).
It describes the points of the relative affine space `𝔸^K` over `Spec R`, for an
arbitrary set `K` of coordinates, through their global coordinate functions. This is
the standard universal property of a polynomial algebra. It formalizes no literature
claim.

All declarations are in `Langlands.AlgebraicGeometry.PolynomialSpecPoints`. Fix
`R : CommRingCat.{u}` and `K : Type`.

- `adjunction_homEquiv_symm_apply`: for `T : Over (Spec R)`, a commutative
  `R`-algebra `B` and `x : T ⟶ (algSpec R).obj (op B)`, the algebra map
  `B → Γ(T, ⊤)` corresponding to `x` under Mathlib's adjunction
  `algΓAlgSpecAdjunction R` sends `b` to `x.left.appTop` of the global function
  `(Scheme.ΓSpecIso (CommRingCat.of B)).inv b`. So it is pullback of global
  functions along `x`.
- `algebra R K` (abbrev) is `MvPolynomial K R` as an object of `CommAlgCat R`, and
  `space R K` (abbrev) is its relative spectrum `(algSpec R).obj (op (algebra R K))`,
  an object of `Over (Spec R)`.
- Instances: the structure morphism of `space R K` is affine
  (`isAffineHom_space`), and it is locally of finite type when `K` is finite
  (`locallyOfFiniteType_space`), because `R → MvPolynomial K R` is of finite type.
- `globalCoord R K κ` is the global function on `space R K` given by the variable
  `MvPolynomial.X κ`.
- `coord x κ`, for a point `x : T ⟶ space R K`, is the pullback
  `x.left.appTop (globalCoord R K κ) : Γ(T.left, ⊤)`.
- `mk v`, for `v : K → Γ(T.left, ⊤)`, is the point corresponding under the
  adjunction to the `R`-algebra map `MvPolynomial.aeval v`.
- `coord_mk`: `coord (mk v) κ = v κ`.
- `ext`: two points `x y : T ⟶ space R K` with `coord x κ = coord y κ` for all `κ`
  are equal.
- `coord_comp`: for `b : T' ⟶ T`, `coord (b ≫ x) κ = b.left.appTop (coord x κ)`.

Together, `mk`, `coord_mk` and `ext` say that `x ↦ coord x` is a bijection from
points `T ⟶ space R K` to families `K → Γ(T.left, ⊤)`. By `coord_comp` this
bijection is natural in `T`. Every test `T` in `Over (Spec R)` is allowed; nothing is
assumed about `T`.

## Proofs

`adjunction_homEquiv_symm_apply` rewrites the inverse adjunction bijection through the
counit (`Adjunction.homEquiv_counit`); the remaining identity holds by definition.
`coord_mk` unfolds `coord` and `globalCoord`, applies
`adjunction_homEquiv_symm_apply` backwards and cancels the bijection with its
inverse, which leaves `MvPolynomial.aeval_X`. For `ext`, the inverse adjunction
bijection is injective, so it suffices that the two corresponding algebra maps out of
`MvPolynomial K R` agree; by `MvPolynomial.algHom_ext` it suffices to compare them on
the variables, where `adjunction_homEquiv_symm_apply` turns them into the given
coordinates. `coord_comp` is `Scheme.Hom.comp_appTop` after unfolding `coord`.
