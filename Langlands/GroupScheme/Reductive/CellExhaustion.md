# Exhaustion of invariant coordinates by products of covariant coordinates

Worker 1628 derives these internal results from standard Hopf-algebra
identities and from localization. They are the algebraic core of an
exhaustion step. Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, third
enlarged edition (1994), Appendix to Chapter 1, Section A, printed p.192,
states that the torus-invariant regular functions on a reductive group form an
increasing union of copies of tensor squares of section modules. That page
gives no argument for this. The argument below, through an open cell and lifts
of invariant functions to the product of the group with itself, is the
author's own reconstruction and is not taken from that page.

Everything is stated for an abstract commutative Hopf algebra with two
bialgebra maps to other Hopf algebras. The geometric input is a list of
explicit hypotheses on one coordinate `d`. For a Borel subgroup `B`, its
opposite `B'` and their intersection, a torus `T`, this list expresses the
standard properties of the big cell `B B'`. The file assumes no Borel
subgroup, big cell, torus or line bundle, and constructs none.

## Setting and notation

Let `k` be a field and `A`, `C`, `C'` commutative Hopf algebras over `k`. `A`
plays the role of the coordinate algebra of an affine group `G`, and `C`, `C'`
those of two subgroups. Bialgebra maps `r : A → C` and `s : A → C'` play the
role of the restriction maps along two subgroup inclusions `i` and `i'`. For a
commutative `k`-algebra `R`, an `R`-point of `G` is a `k`-algebra map
`A → R`, wrapped in Mathlib's `WithConv` so that multiplication is
convolution.

For `χ ∈ C`, the existing `leftCovariantSubspace r χ` consists of the `a ∈ A`
with `(r ⊗ id)(Δ a) = χ ⊗ a`. Pointwise, `a(i(p) z) = χ(p) a(z)`.

## Points form a group

- `pointGroup` is the group structure on the `R`-points: Mathlib's convolution
  monoid, with inverse `f ↦ f ∘ S`, where `S` is the antipode as an algebra map.
  The left inverse law follows from Mathlib's `AlgHom.antipode_id_cancel` and
  `AlgHom.comp_convMul_distrib`. It is a local instance in this file.
- `inv_ofConv_apply` and `one_ofConv_apply` state that `f⁻¹(a) = f(S a)` and
  that the unit point sends `a` to its counit.
- `postcomp h` pushes points forward along an algebra map `h : R → R'`, and is
  a monoid homomorphism. `postcomp_ofConv_apply` evaluates it.
- `pointMap r` restricts points along `r`: a point `c : C → R` goes to `c ∘ r`.
  It is a monoid homomorphism by Mathlib's
  `AlgHom.convMul_comp_bialgHom_distrib`. `pointMap_ofConv_apply` evaluates it,
  and `postcomp_pointMap` states that it commutes with `postcomp`.

## Weights of covariant coordinates

- `pointMap_mul_apply`: if `a ∈ leftCovariantSubspace r χ`, then
  `(pointMap r c * g)(a) = c(χ) g(a)` for all points `c` of `C` and `g` of `A`.
  The proof writes `(c ∘ r) ⊗ g` as `(c ⊗ g) ∘ (r ⊗ id)` and substitutes the
  covariance equation.
- `isUnit_ofConv_weight`: if moreover `a` has counit `1`, then `c(χ)` is a unit
  for every point `c`. Apply the previous lemma to `g = (pointMap r c)⁻¹`.
- `mul_inv_pointMap_apply`: if `S a ∈ leftCovariantSubspace s χ`, then
  `(g * (pointMap s e)⁻¹)(a) = e(χ) g(a)`. This is `pointMap_mul_apply` for
  `S a` at `g⁻¹`, rewritten with `(x y)⁻¹ = y⁻¹ x⁻¹`.
- `isUnit_ofConv_weight'`: under the same hypothesis and counit `1`, `e(χ)` is
  a unit. The antipode preserves the counit.

## Separation by localization

`exists_pow_mul_eq_of_forall_isUnit`: let `T` be a commutative `k`-algebra and
`Q, E, E' ∈ T`. If `τ(E) = τ(E')` for every algebra map `τ : T → R` with
`τ(Q)` a unit, then `Q^m E = Q^m E'` for some `m`. Take `τ` to be the
localization `T → T[1/Q]` and use Mathlib's `IsLocalization.Away.exists_of_eq`.

## The cell difference and cell lifts

Fix `d ∈ A`. Hypotheses used below:

- (C1) `d ∈ leftCovariantSubspace r χ`;
- (C2) `S d ∈ leftCovariantSubspace s ψ`;
- (C3) `d` has counit `1`;
- (Dec) for every `R` and every point `g` of `A` with `g(d)` a unit, there are
  points `b` of `C` and `b'` of `C'` with `g * pointMap s b' = pointMap r b`;
- (Inv) for `f ∈ A`: for every `R`, all points `c` of `C` and `c'` of `C'` with
  `pointMap r c = pointMap s c'`, and every point `g` of `A`,
  `(pointMap r c * g)(f) = g(f)`.

Pointwise, (C1) and (C2) say `d(i(p) z i'(q)⁻¹) = χ(p) ψ(q) d(z)`, and (Dec)
says that every point where `d` is invertible lies in `i(B) i'(B')⁻¹`. (Inv)
says that `f` is left invariant under the intersection of the two subgroups,
encoded as the pairs of points with equal images in `G`.

Results:

- `cellDifference d ∈ A ⊗ A` is the coordinate `(x, y) ↦ d(x y⁻¹)`: the
  convolution of the left inclusion with the inverse of the right inclusion,
  evaluated at `d`.
- `postcomp_productMap_includeLeft` and `postcomp_productMap_includeRight`
  state that the multiplication map of points `X, Y` sends the two inclusions
  to `X` and `Y`. Hence `productMap_cellDifference`: the cell difference
  evaluated at `(X, Y)` is `(X Y⁻¹)(d)`.
- `apply_productMap`: postcomposing a multiplication map of `X, Y` with
  `τ : R → R'` is the multiplication map of `τ ∘ X, τ ∘ Y`.
- `productMap_mul_left_cellDifference` (under C1) and
  `productMap_mul_right_cellDifference` (under C2): translating `X` on the left
  by `pointMap r c` multiplies the cell difference at `(X, Y)` by `c(χ)`, and
  translating `Y` on the left by `pointMap s e` multiplies it by `e(ψ)`.
- `ofConv_pointMap_mul_inv` (under C1–C3): `d(i(b) i'(b')⁻¹) = b(χ) b'(ψ)`.
- `ofConv_inv_pointMap_mul_eq`: under (Inv) at one `R`, two factorizations
  `i(b) i'(b')⁻¹ = i(q) i'(q')⁻¹` give
  `f(i(b)⁻¹ X) = f(i(q)⁻¹ X)` for every point `X`. Indeed `i(b⁻¹ q)` equals
  `i'(b'⁻¹ q')`, and `i(b)⁻¹ X = i(b⁻¹ q) (i(q)⁻¹ X)`.
- `IsCellLift r s d f n F`, for `n ∈ ℕ` and `F ∈ A ⊗ A`, is the proposition: for
  every `R` and all points `X, Y` of `A`, `b` of `C`, `b'` of `C'` with
  `X Y⁻¹ = i(b) i'(b')⁻¹`, the value of `F` at `(X, Y)` equals
  `D(X, Y)ⁿ f(i(b)⁻¹ X)`, where `D = cellDifference d`.
- `productMap_comp_include`: for an algebra map `loc : A ⊗ A → T`, the
  multiplication map of `loc ∘ includeLeft` and `loc ∘ includeRight` is `loc`.
- `exists_isCellLift` (under C1–C3, Dec, Inv): there are `n` and `F` with
  `IsCellLift r s d f n F`. Proof: let `R₀ = (A ⊗ A)[1/D]` and `X₀, Y₀` the two
  inclusions into `R₀`. Then `(X₀ Y₀⁻¹)(d)` is the image of `D`, a unit, so
  (Dec) gives `X₀ Y₀⁻¹ = i(b₀) i'(b₀')⁻¹`. Write
  `f(i(b₀)⁻¹ X₀) = F / Dⁿ` in `R₀`. Given `(X, Y)` with
  `X Y⁻¹ = i(b) i'(b')⁻¹`, the value of `D` at `(X, Y)` is
  `b(χ) b'(ψ)`, a unit. So the multiplication map of `X, Y` extends to
  `τ : R₀ → R` with `τ ∘ X₀ = X` and `τ ∘ Y₀ = Y`. Pushing the factorization
  forward along `τ` and using `ofConv_inv_pointMap_mul_eq` gives the
  identity.
- `IsCellLift.mul_left` and `IsCellLift.mul_right`: at points `X, Y` of a fixed
  `R` where `D` is a unit, and under (C1), resp. (C2), and (Dec) at `R`,
  translating `X` by `pointMap r c` multiplies `F(X, Y)` by `c(χ)ⁿ`, and
  translating `Y` by `pointMap s e` multiplies it by `e(ψ)ⁿ`.
- `mul'_eq_productMap`: multiplication `A ⊗ A → A` is the multiplication map
  of two copies of the identity.
- `mul'_cellDifference` (under C3): the cell difference multiplies to `1`,
  since `d(x x⁻¹) = d(1) = 1`.
- `IsCellLift.mul'` (under C3): a cell lift of `f` multiplies to `f`. Evaluate
  at `X = Y = id`, `b = b' = 1`.
- `IsCellLift.cellDifference_pow_mul`: `Dʲ F` is a cell lift with exponent
  `n + j`.

## Universal test points

`pointMap_toConv_comp_mul_apply` states that for an algebra map
`θ : C ⊗ A → R`, the convolution of `pointMap r (θ ∘ includeLeft)` with
`θ ∘ includeRight`, at `a`, is `θ((r ⊗ id)(Δ a))`. The four lemmas
`productMap_testLeft`, `productMap_testLeft'`, `productMap_testRight` and
`productMap_testRight'` use points with values in `(C ⊗ A) ⊗ A` and
`A ⊗ (C' ⊗ A)`. They concern the covariance equations of
`Reductive/CovariantKunneth.lean` for the first and the second factor of a
tensor `F ∈ A ⊗ A`. The left side of each equation is the value of `F` at
universal points, one of them translated by a universal restricted point. The
right side, for weight `μ`, is the universal image of `μ` times the value of
`F` at the untranslated universal points.

## Covariance of cell lifts

Assume `IsCellLift r s d f n F`.

- `IsCellLift.exists_pow_mul_eq_left` (under C1, Dec) and
  `IsCellLift.exists_pow_mul_eq_right` (under C2, Dec): at any points `X, Y`
  and `c`, resp. `e`, the two sides of `IsCellLift.mul_left`, resp.
  `IsCellLift.mul_right`, agree after multiplication by `D(X, Y)^m` for some
  `m`. Apply the separation lemma; the two sides agree after every algebra map
  making `D(X, Y)` a unit, by `apply_productMap`.
- `IsCellLift.exists_rTensor_eq` (under C1, Dec): there is `m` such that for
  every `t`, `D^(m+t) F` is covariant of weight `χ^(n+m+t)` in its first factor,
  in the form required by `mul'_mem_mul_leftCovariantSubspace`.
  `IsCellLift.exists_lTensor_eq` (under C2, Dec) gives the same in the second
  factor with weight `ψ^(n+m+t)`. Both apply the previous lemmas at the
  universal test points.

## Main results

- `one_mem_mul_leftCovariantSubspace` (under C1–C3): `1` lies in
  `leftCovariantSubspace r χ * leftCovariantSubspace s ψ`. The cell difference
  is covariant of weight `χ` in its first factor and `ψ` in its second, and
  multiplies to `1`, so `mul'_mem_mul_leftCovariantSubspace` applies.
- `exists_mem_mul_leftCovariantSubspace` (under C1–C3, Dec, Inv): there is `N`
  with `f ∈ leftCovariantSubspace r (χ ^ N) * leftCovariantSubspace s (ψ ^ N)`.
  Take a cell lift `F` with exponent `n`, the exponents `m₁` and `m₂` of the
  two covariance lemmas, and `N = n + m₁ + m₂`. Then `D^(m₁+m₂) F` is a cell
  lift of `f`, covariant of weight `χ^N` and `ψ^N` in its two factors, and
  multiplies to `f`.

## Density of the cell

- `ofConv_pointMap_mul_inv_apply`: the value of `w ∈ A` at
  `i(b) i'(b')⁻¹` is the value at `(b, b')` of Worker 1330's
  `differenceComorphism r s w`, the comorphism of `(p, q) ↦ i(p) i'(q)⁻¹`.
- `injective_differenceComorphism`: under (Dec) and the hypothesis that `d` is
  left regular (a non-zero-divisor), `differenceComorphism r s` is injective.
  If `w` lies in its kernel, take the localization `A → A[1/d]` as a point.
  By (Dec) it is `i(b) i'(b')⁻¹`, so the previous lemma makes `w` vanish in
  `A[1/d]`. Hence `dⁿ w = 0` for some `n`, and `w = 0`.

## Scope

The results are purely algebraic. Nothing here shows that hypotheses (C1)–(C3),
(Dec) or left regularity of `d` hold for any particular subgroups. For
coordinate algebras of actual group schemes, translating (Inv) and (Dec) from
scheme points to algebra-map points, and identifying the antipode with
inversion, are left to later units. No statement about irreducibility,
dimension or injectivity of multiplication maps is made here.
