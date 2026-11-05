# Submersive and smooth algebra maps are open on points over complete fields

Author: Worker 1505.

This is a derived helper module for the proof of
[SmoothOpenMapStatement](SmoothOpenMapStatement.md). It works on the published
algebra-point carrier `AlgPoint K A K` of [Affine](Affine.md), the set of
`K`-algebra maps `A → K` with the evaluation topology. It introduces no new
point carrier, topology or global instance. All declarations are in the
namespace `Langlands.AlgebraicGeometry.PointTopology.SubmersiveOpen`.

## Results

Let `K` be a nontrivially normed field, complete where stated. Let `A` and `B`
be commutative `K`-algebras with `Algebra A B` and `IsScalarTower K A B`.

- `isOpenMap_precomp_of_submersivePresentation`: if
  `P : Algebra.SubmersivePresentation A B ι σ` has finitely many variables and
  relations, then restriction
  `AlgPoint.precomp (IsScalarTower.toAlgHom K A B) : AlgPoint K B K → AlgPoint K A K`
  is an open map.
- `isOpenMap_precomp_of_isStandardSmooth`: the same conclusion under
  `Algebra.IsStandardSmooth A B`. It obtains a finite submersive presentation
  from the definition and applies the previous theorem.
- `isOpenMap_precomp_of_smooth`: for `A B : Type u`, any `K`-algebra map
  `φ : A →ₐ[K] B` whose underlying ring map is `RingHom.Smooth` gives an open
  map `AlgPoint.precomp φ`.

There are no finite-type, noetherian or nonemptiness hypotheses on `A` or `B`.
The algebraic lemmas below assume only a field `K`.

## Coefficient variables

For a presentation `P` of `B` over `A`, `CoeffIndex P` indexes the pairs of a
relation `j` and a monomial in the support of `P.relation j`; it is finite when
there are finitely many relations. `coeffVal P` gives the corresponding
coefficients in `A`. `genericRelation P j` is the polynomial over `K` in the
variables `CoeffIndex P ⊕ ι` obtained from `P.relation j` by replacing each
coefficient with its own new variable. `specialize P` substitutes the actual
coefficients `C (coeffVal P k)` for these variables.

- `specialize_genericRelation`: `specialize P (genericRelation P j) = P.relation j`.
  The proof expands both sides over the support and uses `monomial_eq`.
- `specialize_pderiv`: specialization commutes with partial derivatives in the
  ordinary variables `Sum.inr i`. The proof is polynomial induction with the
  Leibniz rule; coefficient variables specialize to constants.
- `eval_elim_eq`: evaluating at coefficient values `y (coeffVal P k)` and
  variable values `v` agrees with evaluating the specialization, mapped along
  the point `y : A →ₐ[K] K`, at `v`. Both sides are ring maps agreeing on
  constants and variables.
- `eval_map_restrict`: for `x : B →ₐ[K] K`, evaluating at the coordinates
  `x (P.val i)`, after mapping along the restriction of `x` to `A`, is `x`
  applied to the image of the polynomial in `B`.

## Lifting solutions to points

`evalMap y v` is the `K`-algebra map `q ↦ eval v (map y q)` on polynomials over
`A`. If `v` solves all relations with coefficients mapped along `y`,
`liftPoint P y v hv : B →ₐ[K] K` is obtained by `AlgHom.liftOfSurjective` from
the surjection `aeval P.val`. Its kernel is spanned by the relations
(`P.ker_eq_ker_aeval_val`, `P.span_range_relation_eq_ker`), and `evalMap y v`
kills each relation. `liftPoint_aeval` computes it on images of polynomials,
`liftPoint_comp` shows that it restricts to `y` on `A`, and `liftPoint_self`
shows that the lift of the coordinates of a point `x` is `x` itself.

## Implicit function theorem with parameters

`eventually_exists_solution`: let `K` be complete, `P` a finite submersive
presentation, `x : B →ₐ[K] K`, and `W` a neighbourhood of the coordinates
`v₀ = (x (P.val i))_i`. For every coefficient vector `a` near the coefficient
values `a₀ = (x (coeffVal P k))_k` of `x`, some `v ∈ W` satisfies
`eval (Sum.elim a v) (genericRelation P j) = 0` for all relations `j`.

The proof follows the absolute argument of
`Langlands.RingTheory.LocalFieldDensity.eventually_exists_algHom`, with the
coefficient variables as extra coordinates. Let `w₀ = Sum.elim a₀ v₀` and let
`τ` be the free variables outside the range of `P.map`. The map

```text
Φ : (CoeffIndex P ⊕ ι → K) → (CoeffIndex P ⊕ (σ ⊕ τ) → K)
Φ w = (w on coefficient variables, eval w (genericRelation P j), w on free variables)
```

has strict derivative `D` at `w₀`, built from coordinate projections and the
Library's `hasStrictFDerivAt_polynomial_eval`. `D` is injective. Its
coefficient and free components force those coordinates of a kernel vector
`h` to vanish. The relation components then reduce, by `Fintype.sum_sum_type`
and reindexing along the injective `P.map`, to the square system
`(eval w₀ (pderiv (Sum.inr (P.map k)) (genericRelation P j)))_{j,k}`. By
`eval_elim_eq`, `specialize_pderiv` and `eval_map_restrict`, its entries are
`x (aeval P.val (pderiv (P.map k) (P.relation j)))`. So the matrix is the
transpose of the image of `P.jacobiMatrix` under `x ∘ aeval P.val`, and its
determinant is `x P.jacobian`, a unit. The two sides have equal finite
dimension, since `σ ⊕ τ ≃ ι`. Hence `D` is a continuous linear equivalence, and
Mathlib's `HasStrictFDerivAt.map_nhds_eq_of_equiv` shows that `Φ` maps
neighbourhoods of `w₀` onto neighbourhoods of `Φ w₀`. Relations vanish at `w₀`,
so `Φ w₀ = (a₀, 0, v₀ on free variables)`. For `a` near `a₀` the vector
`(a, 0, v₀ on free variables)` is the image of some `w` whose ordinary
coordinates lie in `W`; then `w = Sum.elim a v` with `v ∈ W` solves the
generic relations.

## Openness

For `isOpenMap_precomp_of_submersivePresentation`, take a point `x` and a set
`S` whose preimage is a neighbourhood of `x`. The solution locus `T` consists
of the pairs `(y, v)` of a point of `A` and a vector solving the relations with
coefficients mapped along `y`. The lift map `T → AlgPoint K B K` is continuous:
by `AlgPoint.continuous_iff` and surjectivity of `aeval P.val`, each evaluation
is `(y, v) ↦ eval v (map y q)`, which `continuous_eval_map` expands as a finite
sum of products of point evaluations and coordinates. The lift of
`(restriction of x, v₀)` is `x`. So the preimage of the neighbourhood is a
neighbourhood in `T`, and it contains `T ∩ (U₁ × W)` for neighbourhoods `U₁` of
the restriction of `x` and `W` of `v₀`. Coefficient values depend continuously
on `y`. By `eventually_exists_solution`, every `y` near the restriction of `x`
lies in `U₁` and has some `v ∈ W` solving the generic relations at
`(y (coeffVal P k))_k`. By `specialize_genericRelation` and `eval_elim_eq`,
`(y, v) ∈ T`; its lift lies in the preimage and restricts to `y`. Hence `S` is
a neighbourhood of the restriction of `x` (`isOpenMap_iff_nhds_le`).

For `isOpenMap_precomp_of_smooth`, Mathlib's
`RingHom.smooth_iff_locally_isStandardSmooth` gives a set `s ⊆ B` spanning the
unit ideal such that each composite `A → B → B_t`, with `B_t` the localization
away from `t`, is standard smooth. The image of an open `O` is the union over
`t ∈ s` of the images of the open preimages of `O` in `AlgPoint K B_t K` under
restriction along `A → B_t`. Every point `x` of `B` is unit-valued at some
`t ∈ s`; otherwise `x` would vanish on the ideal spanned by `s`, which contains
`1`. The Library's `range_precomp_localization` and `unit_powers_iff` then lift
`x` to `B_t`. With the `A`-algebra structure on `B_t` given by the composite,
which forms a scalar tower over `K`, each piece is open by the standard-smooth
case.

## Provenance

This is internal derived infrastructure. It combines Mathlib's inverse function
theorem, submersive presentations, local standard smoothness of smooth ring
maps and `AlgHom.liftOfSurjective` with the Library's polynomial calculus,
absolute implicit-points argument and algebra-point localization API. The
mathematical route is the implicit-function argument for openness of smooth
maps on points recalled in Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), printed p. 11. Conrad reduces to étale maps and continuity of
simple roots; this implementation instead applies the inverse function theorem
directly to a local standard-smooth presentation.
