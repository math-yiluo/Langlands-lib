# Coordinate actions on vector groups are given by additive polynomials

Let `b` be an action of a group scheme `H` on a vector group `V` over a field
`k`. Fix coordinates `e` of `V` with values in `n`-tuples of global sections.
This module expresses the action of each point of `H` in these coordinates. It
shows that the resulting map on coordinate vectors is additive, natural, and
given by polynomials that are additive on every algebra. In characteristic `p`
those polynomials are `p`-polynomials. Everything is in namespace
`Langlands.GroupScheme.RelativeRoot`.

## The coordinate action

For a commutative `k`-algebra `A` and a point `h` of `H` over `A`:

- `coordinateAction b e h : (Fin n → A) →+ (Fin n → A)` sends `x` to the
  coordinates of `h · e⁻¹(x)`. Here `e` is the published
  `vectorAffineCoordinates e A` on the affine test `Spec A`. The map is additive
  because the action is by group automorphisms (`act_one`, `act_mul_right`).
  `coordinateAction_apply` unfolds the definition.
- `coordinateAction_vectorAffineCoordinates`: the coordinate action applied to
  the coordinates of a point `v` gives the coordinates of `h · v`.
- `coordinateAction_one` and `coordinateAction_mul`: the identity point acts
  trivially, and `h h'` acts as `h` after `h'` (`act_one_left`, `act_mul_left`).

From here on the coordinates are assumed natural
(`he : IsNaturalVectorCoordinates e`).

- `vectorAffineCoordinates_symm_naturality`: for a `k`-algebra map
  `f : A →ₐ[k] B`, extending coefficients along `f` sends the point with
  coordinates `x` to the point with coordinates `f ∘ x`.
- `coordinateAction_naturality`: the coordinate action of the extended point on
  `f ∘ x` is `f` applied to the coordinate action of `h` on `x`. The proof
  combines the previous lemma with the published naturality of the action on
  affine points (`affineAct_naturality`).

## Coordinate polynomials

- `coordinatePolynomials b e h : Fin n → MvPolynomial (Fin n) A` is the
  coordinate action of `h`, extended to the polynomial algebra
  `A[X_0, …, X_{n-1}]`, on the universal vector `(X_0, …, X_{n-1})`.
- `coordinateAction_eq_aeval`: let `C` be a commutative algebra over `A`, and
  over `k` compatibly. The coordinate action of `h` extended to `C` sends
  `z : Fin n → C` to the evaluation of the coordinate polynomials at `z`. Apply
  naturality to the evaluation map `A[X] → C` at `z`.
  `coordinateAction_eq_aeval_self` is the case `C = A`.
- `coordinatePolynomials_additive`: each coordinate polynomial is additive on
  every commutative `A`-algebra `B`. Give `B` the `k`-algebra structure through
  `A`. Then evaluation at `x + y` is the extended coordinate action at `x + y`,
  which is additive.
- `coordinatePolynomials_naturality`: the coordinate polynomials of the point
  extended along `f : A →ₐ[k] B` are the images of those of `h` under the
  coefficient map `MvPolynomial.map f`.

## Characteristic `p`

Let `p` be a prime with `CharP k p`. Then `p = 0` in every `k`-algebra.

- `exists_coordinatePolynomials_eq_sum_pow`: there are `N` and `c i j s` in `A`
  with `coordinatePolynomials b e h i = ∑ j, ∑ s < N, C (c i j s) * X j ^ p ^ s`.
  Apply `AdditiveSupport.MvPolynomial.exists_eq_sum_pow_of_additive` to each
  coordinate polynomial, and take a common bound `N` for all `i`.
- `exists_coordinateAction_eq_sum_pow`: with the same data, the coordinate
  action of `h` extended to any compatible `A`-algebra `C` is
  `z ↦ (∑ j, ∑ s < N, c i j s · z j ^ p ^ s)_i`. One `p`-polynomial matrix thus
  describes the action over all such `C`.

## Provenance

These lemmas are internal to the proof of
`TorusVectorActionLinearizationStatement`. They formalize the standard fact that,
in characteristic `p`, a group scheme acts on a vector group through
`p`-polynomials. In Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed., this
corresponds to Proposition B.1.3, printed p.562 (PDF p.588): homomorphisms
`Ga^n → Ga` are exactly the maps given by `p`-polynomials. A related idea appears in
the proof of Proposition B.4.1, printed p.575 (PDF p.601), which uses the functor
`Hom(U, Ga)` of additive functions. The source argument for Theorem B.4.3 does not
contain these coordinate lemmas, which belong to the project's own derivation. The
universal-vector construction is the usual Yoneda argument, here phrased with the
published `vectorAffineCoordinates` and affine points `Lie.AffinePoints`.
