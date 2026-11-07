# Bilinearity of equivariant pairings of weight vector groups

This module shows that certain pairings `P : V × V ⟶ W` of vector groups over a field `k` are
bilinear in vector coordinates. Here `V` and `W` are group schemes over `Spec k` with natural
vector coordinates of weights `χ` and `2 • χ`, for a split torus `S`, and `χ ≠ 0`. The
pairing must be multiplicative in each argument and must intertwine the two torus actions.
Then `P` is additive and linear over `Γ(T, 𝒪_T)` in each argument separately, on every test
scheme `T`. Characteristic zero is not assumed. The intended application is the commutator
pairing `U_a / U_{2a} × U_a / U_{2a} ⟶ U_{2a}` of a multipliable relative root `a`. This
module does not treat that application.

The argument is internal; it is not taken from a reference. It extends the Laurent-polynomial
argument of the published `coordinateAffineAction_smul` (module
`GroupScheme/Rational/VectorActionWeightCommuting`) from one variable to two.

## Setting and notation

All declarations live in namespace `Langlands.GroupScheme.RelativeRoot`. The data are:

- `e : ∀ T, (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))`, vector coordinates on `V`;
- `e' : ∀ T, (T ⟶ W.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))`, vector coordinates on `W`;
- `P : V.X ⊗ V.X ⟶ W.X`, a morphism of schemes over `Spec k` (the tensor is the cartesian
  product). The pair of `T`-points `x, y` of `V` gives the `T`-point `lift x y ≫ P` of `W`;
- `c` and `c'`, automorphic actions of `S` on `V` and on `W`.

The coordinate hypotheses come from the published `GroupScheme/Rational/WeightSemigroupStatement`.
`IsNaturalVectorCoordinates e` says that the coordinates commute with pullback along every
test morphism. `IsWeightVectorCoordinates c χ e` adds that a `T`-point `s` of `S` acts on
coordinates as multiplication by the unit `χ(s) ∈ Γ(T, 𝒪_T)ˣ`.

The equivariance hypothesis is

`hP : ∀ T (s : T ⟶ S.X) (x y : T ⟶ V.X), lift (c.act s x) (c.act s y) ≫ P = c'.act s (lift x y ≫ P)`.

## Definitions

- `coordinatePairing e e' P x y` (definition). For a commutative `k`-algebra `A` and tuples
  `x y : Fin d → A`, take the points of `V` over `Spec A` with coordinates `x` and `y`. The
  value is the coordinate tuple in `Fin m → A` of the image of that pair under `P`. The
  coordinates over coefficient algebras are the published `vectorAffineCoordinates`
  (module `GroupScheme/Rational/VectorLieCoordinates`).
- `IsBilinearVectorPairing e e' P` (definition, a `Prop`). The condition is quantified over
  every test scheme `T` over `Spec k`, all `T`-points `x, x', y, y'` of `V`, and every
  `r ∈ Γ(T, 𝒪_T)`, and has four conjuncts:
  1. `e'(P(x x', y)) = e'(P(x, y)) + e'(P(x', y))`;
  2. `e'(P(x, y y')) = e'(P(x, y)) + e'(P(x, y'))`;
  3. `e'(P(x_r, y)) = r • e'(P(x, y))`, where `x_r` is the point with coordinates
     `r • e(x)`;
  4. `e'(P(x, y_r)) = r • e'(P(x, y))`, where `y_r` is the point with coordinates
     `r • e(y)`.

  Here `e(x)` and `e'(z)` denote the coordinate tuples `(e T x).toAdd` and `(e' T z).toAdd`.

## Laurent-polynomial lemmas

These lemmas hold for any commutative ring `A`. `T n` is the monomial `tⁿ` in `A[t, t⁻¹]`,
`invert` is the substitution `t ↦ t⁻¹`, `toLaurent : A[X] → A[t, t⁻¹]` is the inclusion and
`trunc` keeps the terms of nonnegative degree.

- `trunc_T_two_mul_invert_toLaurent q`: `trunc (t² q(t⁻¹)) = q₀ X² + q₁ X + q₂`, where `qᵢ` is
  the coefficient of `Xⁱ` in `q`. The proof is by induction over sums of monomials.
- `eq_of_toLaurent_eq_T_two_mul_invert h`: if `p(t) = t² q(t⁻¹)`, then
  `p = q₀ X² + q₁ X + q₂`. Apply `trunc` to both sides.
- `toLaurent_eq_T_two_mul_invert_symm h`: the relation `p(t) = t² q(t⁻¹)` implies
  `q(t) = t² p(t⁻¹)`.
- `eq_C_mul_X_of_toLaurent_eq_T_two_mul_invert h hp hq`: if `p(t) = t² q(t⁻¹)` and
  `p₀ = q₀ = 0`, then `p = p₁ X` and `q = p₁ X`. Compare coefficients in the two
  reflected forms.
- `laurentPowerAlgHom_one_apply p`: the substitution `X ↦ t` (the published
  `laurentPowerAlgHom A 1`) agrees with `toLaurent`.
- `aevalTower_laurentCAlgHom_T_neg_one p`: the substitution `X ↦ t⁻¹` agrees with
  `invert ∘ toLaurent`. Both are proved by extension of ring homomorphisms from `A[X]`.

## Statements about the coordinate pairing

- `coordinatePairing_naturality he he' f x y`. Assume `IsNaturalVectorCoordinates e` and
  `IsNaturalVectorCoordinates e'`. Then, for every map of `k`-algebras `f : A →ₐ[k] B`,
  `coordinatePairing (f ∘ x) (f ∘ y) = f ∘ coordinatePairing x y`.
- `coordinatePairing_zero_left h1 y`, `coordinatePairing_zero_right h1' x`. If
  `lift 1 y ≫ P = 1` for all `T, y`, then `coordinatePairing 0 y = 0`, and symmetrically in
  the second argument.
- `coordinatePairing_weight_smul he he' hP s hw hw' x y`. Assume
  `IsWeightVectorCoordinates c χ e`, `IsWeightVectorCoordinates c' ψ e'` and `hP`. Let `s`
  be a point of `S` over `Spec A`, and let `w` and `w'` be the values of `χ` and `ψ` at `s`
  (hypotheses `hw` and `hw'`). Then `coordinatePairing (w • x) (w • y) = w' • coordinatePairing x y`.
- `coordinatePairing_smul_smul hS hχ he he' hP r x y` (**homogeneity**). Assume
  `IsSplitTorus S.toGrp`, `χ ≠ 0`, weight coordinates of weights `χ` on `V` and `2 • χ` on
  `W`, and `hP`. Then for every `k`-algebra `A`, `r ∈ A` and `x, y : Fin d → A`,
  `coordinatePairing (r • x) (r • y) = r² • coordinatePairing x y`.
- `coordinatePairing_smul hS hχ he he' hP h1 h1' r x y` (**scalar linearity**). Under the
  hypotheses of homogeneity together with `h1` and `h1'` (triviality at the identity in
  each argument), the result has two parts:
  `coordinatePairing (r • x) y = r • coordinatePairing x y` and
  `coordinatePairing x (r • y) = r • coordinatePairing x y`.
- `coordinatePairing_global he he' T x y`. Under natural coordinates, for every test scheme
  `T` and `T`-points `x, y` of `V`, `e'(P(x, y))` equals `coordinatePairing e(x) e(y)` computed
  over the `k`-algebra `Γ(T, 𝒪_T)` (written `((algΓ k).obj T).unop` in Lean).
- `isBilinearVectorPairing_of_equivariant hS hχ he he' hmul_left hmul_right hP`
  (**bilinearity**). Assume `IsSplitTorus S.toGrp`, `χ ≠ 0`,
  `IsWeightVectorCoordinates c χ e`, `IsWeightVectorCoordinates c' (2 • χ) e'`, and `hP`.
  Assume further that `P` is multiplicative in each argument on all test points:
  `hmul_left : lift (x * x') y ≫ P = (lift x y ≫ P) * (lift x' y ≫ P)` and
  `hmul_right : lift x (y * y') ≫ P = (lift x y ≫ P) * (lift x y' ≫ P)`. Then
  `IsBilinearVectorPairing e e' P`.

## Proofs

**Naturality.** The published `vectorAffineCoordinates_naturality` identifies the image
under `f` of the coordinates of a point with the coordinates of its base change along
`Spec f`. Base change commutes with forming `lift x y ≫ P`.

**Weight scaling.** By `vectorAffineCoordinates_act`, the point with coordinates `w • x` is
`c.act s` applied to the point with coordinates `x`. Then `hP` moves the action through `P`,
and the weight coordinates of `W` turn `c'.act s` into multiplication by `w'`.

**Homogeneity.** The published `IsSplitTorus.exists_pairing_eq_pos` gives a cocharacter `ζ`
with `⟨χ, ζ⟩ = D > 0`, so `⟨2 • χ, ζ⟩ = 2D`. Put `Q = coordinatePairing (X • x) (X • y)` over
`A[X]`. Base change along `X ↦ t^D` into `A[t, t⁻¹]` gives the pairing at the tuples
`t^D • x` and `t^D • y`. Weight scaling at the torus point `ζ(t)` (the published
`laurentCocharacterPoint`, with `laurentCocharacterPoint_value`) shows that this equals
`t^{2D} • coordinatePairing x y`. Since `X ↦ t^D` is injective
(`laurentPowerAlgHom_injective`), `Q = X² • coordinatePairing x y`. Substituting `X ↦ r`
finishes the proof.

**Scalar linearity.** Over `A[X]`, put `G = coordinatePairing (X • x) y` and
`K = coordinatePairing x (X • y)`, with `x` and `y` read as constant tuples. Substitute
`X ↦ t` in `G` and `X ↦ t⁻¹` in `K`. Then homogeneity, applied over `A[t, t⁻¹]` to the scalar
`t` and the tuples `x` and `t⁻¹ • y`, gives `G(t) = t² K(t⁻¹)` coordinatewise. Substituting
`X ↦ 0` and using `h1`, `h1'` shows that the constant terms of `G` and `K` vanish. The
Laurent lemma then gives `G = K = c X` for one tuple `c`. Substituting `X ↦ r` and `X ↦ 1`
gives `coordinatePairing (r • x) y = r • c = r • coordinatePairing x y`, and the same for `K`.

**Scheme tests.** For a test scheme `T`, let `a : T ⟶ Spec Γ(T, 𝒪_T)` be the affinization
unit. Then a point `x` of `V` over `T` is `a` composed with the point over `Spec Γ(T, 𝒪_T)`
that has the same coordinates (`vectorAffineCoordinates_unit_comp`). This identifies
`e'(P(x, y))` with the coordinate pairing over `Γ(T, 𝒪_T)`.

**Bilinearity.** Additivity in each argument is `hmul_left` or `hmul_right` followed by
multiplicativity of `e'`. In a group, `z = z * z` forces `z = 1`, so multiplicativity gives
`h1` and `h1'`. Scalar linearity over `Γ(T, 𝒪_T)` follows from `coordinatePairing_global`
and `coordinatePairing_smul`.

## Scope

The module proves bilinearity of such a pairing in the given coordinates. It does not
construct a commutator pairing, does not apply the result to root groups, and does not
identify the pairing with a hermitian or trace form.
