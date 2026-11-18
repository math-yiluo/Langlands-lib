# The split Cayley automorphism group scheme has trivial centre

Notation as in `RootGroups.md` and `Points.md`. Zorn's algebra has coordinates `e₀, …, e₇`, where
`e₀` and `e₇` are the two diagonal idempotents, `e₁, e₂, e₃` span the `u`-block and
`e₄, e₅, e₆` span the `v`-block. The unit is `e₀ + e₇`. `x_α(r) = rootMatrix α r` is the root
element for the root `α`. `Aut_K` is the automorphism group scheme of Zorn's algebra over a field
`K`.

## Rigidity of central matrices (any commutative ring)

- `rootFun_mulVec_of_commute`: if a matrix `g` commutes with `x_α(1)`, then
  `x_α(1)(g v) = g(x_α(1) v)` for every vector `v`.
- `centerRigidity : CenterRigidityStatement`: over every commutative ring `A`, an automorphism
  matrix `g` of Zorn's algebra that commutes with all twelve `x_α(1)` is the identity. The Lean
  proof is a direct computation.
  1. Put `w = g e₀`. The long root elements `x_{l12}(1)`, `x_{l21}(1)`, `x_{l13}(1)` and
     `x_{l31}(1)` fix `e₀`, so they fix `w`. Comparing coordinates gives
     `w₁ = w₂ = … = w₆ = 0`.
  2. The short root elements satisfy `x_{u1}(1) e₀ = e₀ + e₁` and `x_{v1}(1) e₀ = e₀ + e₄`, so
     `g e₁ = x_{u1}(1) w - w` and `g e₄ = x_{v1}(1) w - w`. With step 1 these equal
     `(w₀ - w₇) e₁` and `(w₀ - w₇) e₄`.
  3. In Zorn's algebra `e₁ e₄ = e₀` and `e₄ e₁ = e₇ = 1 - e₀`. Applying `g`, which is
     multiplicative and fixes `1`, gives `(w₀ - w₇)² e₀ = w` and `(w₀ - w₇)² e₇ = 1 - w`. The
     `e₇`-coordinate of the first identity gives `w₇ = 0`. The `e₀`-coordinate of the second
     gives `w₀ = 1`. So `g e₀ = e₀`.
  4. For each `i = 1, …, 6` there is a short root `α` with `x_α(1) e₀ = e₀ + eᵢ` (namely
     `u1, u2, u3, v1, v2, v3`). As in step 2, `g eᵢ = x_α(1) e₀ - e₀ = eᵢ`. Finally
     `g e₇ = g(1 - e₀) = e₇`. So `g` fixes every coordinate vector, and `g = 1`.

  An earlier draft of `CenterRigidityStatement` also assumed that `g` commutes with the torus.
  That hypothesis is not needed, so it was removed.

## The centre of the group scheme (over a field)

- `rootOnePoint T α`: the `T`-point of `Aut_K` with matrix `x_α(1)`, for a `K`-scheme `T`.
  `pointsEquiv_rootOnePoint` states that its matrix is `rootMatrix α 1`.
- `center_eq_bot K`: the scheme-theoretic centre (the published `center`) of `Aut_K` is the
  trivial subgroup functor. A `T`-point `x` of the centre commutes with every `T`-point, in
  particular with each `rootOnePoint T α` (published `commute_of_mem_center`). The group
  isomorphism `pointsEquiv` turns this into commutation of the matrix of `x` with every
  `x_α(1)` over `Γ(T, ⊤)`. The matrix of `x` is an automorphism matrix, so it is the identity by
  `centerRigidity`. Since `pointsEquiv` is injective, `x = 1`.
