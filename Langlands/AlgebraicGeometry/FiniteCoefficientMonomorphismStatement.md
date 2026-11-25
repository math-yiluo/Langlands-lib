# Monicity over finite coefficient subalgebras

This internal statement supplies eventual monicity in the
arbitrary-base limit reduction for reductive group monomorphisms.

For arbitrary commutative rings `R` and `A` with an `R`-algebra structure,
let `f : X ⟶ Y` be a map of schemes over `Spec R`. Assume that `X` is of
finite type over `Spec R`, expressed by quasi-compactness and local finite
type, and that `Y` is quasi-separated over `Spec R`. If the specified map
becomes a monomorphism over `A`, it is already a monomorphism after base
change to some finitely generated `R`-subalgebra of `A`. This subalgebra can
contain any prescribed finite subset of `A`. The proposition is uniform
in every universe.

Its provenance is the equality-of-morphisms form of finite coefficient
descent already published in
`AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType`.
The kernel pair of `f` is quasi-compact over the coefficient base: `f` is
quasi-compact because its source is quasi-compact and its target is
quasi-separated over that base. Monicity after base change says that the
two kernel-pair projections agree after base change. Their target `X` is
locally of finite type, so this equality descends to finite coefficients.
Base change preserves the kernel pair, and equality of its projections
is equivalent to monicity.

This is an internal scheme-level prerequisite, with no reductivity,
smoothness, flatness or affine-target premise. It does not itself
construct group models or prove the closed-immersion theorem.
