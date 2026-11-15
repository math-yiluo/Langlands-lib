# Semilinear coordinates on rational root-group points

## Purpose and provenance

This module is internal to the proof of
`Langlands.Geometry.Building.UnramifiedZeroJumpDescentStatement` (Task 6754). It contains
one proposition, `Langlands.Geometry.Building.RootGroupLinearization`. That proposition packages
the linear structure of the root group `U_{α_K}(K)` that the Galois descent of filtration jumps
needs. Mathematically it collects standard facts about root groups of a split torus. In the
setting of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, §2.6.8 (printed p. 95; PDF p. 126), concerning root groups `U_a`
and their filtration `U_{2a} ⊂ U_a`, the quotient `U_a/U_{2a}` and `U_{2a}` are vector groups with
the Lie algebras `𝔤_a`, `𝔤_{2a}`. Coordinates over the base field are Galois equivariant, and
the torus acts on `𝔤_a` through `a`. The proposition is stated for an arbitrary field extension
`K/k` and an arbitrary valuation `v` on `K` with values in a linearly ordered commutative group
with zero. The definition only states the proposition and proves nothing.

## Notation

Fix fields `k ⊆ K` and the base map `b = algebraBaseMap k K : Spec K ⟶ Spec k`. Let `G` be an
affine `k`-group scheme, `S` a commutative `k`-group scheme, `iS : S → G` a homomorphism, and
`α` a character of `S`. Write

* `G_K`, `S_K`, `j_K iS` for the base changes along `b`, and `α_K` for the base-changed
  character;
* `U = rootGroupPoints (j_K iS) α_K`, the rational points `U_{α_K}(K)` of the root subgroup
  functor;
* `U₂ = doubleRootGroupPoints (j_K iS) α_K`, which is `U_{2α_K}(K)` if `2α_K` is a relative
  root of `(G_K, S_K)` and the trivial subgroup otherwise;
* `σ · x = rationalConjugate k K G σ x`, the action of `σ ∈ Aut(K/k)` on `G_K(K)` through the
  coefficients;
* `T_t = rationalPoints.map (j_K iS) t ∈ G_K(K)` for a point `t ∈ S_K(K)`.

## Statement

`RootGroupLinearization iS α v` holds when there are natural numbers `n`, `m`, `d` and maps
`q : G_K(K) → K^n` and `e : G_K(K) → K^m` (`K^n` is `Fin n → K`) with:

1. `d = 1` or `d = 2`.
2. `q (x * y) = q x + q y` for `x, y ∈ U`.
3. For `x ∈ U`: `q x = 0` if and only if `x ∈ U₂`.
4. `e (x * y) = e x + e y` for `x, y ∈ U₂`.
5. For `x ∈ U₂`: `e x = 0` implies `x = 1`.
6. `σ · x ∈ U` for every `σ ∈ Aut(K/k)` and `x ∈ U`.
7. `q (σ · x) = (i ↦ σ (q x i))` for `x ∈ U`.
8. `e (σ · x) = (i ↦ σ (e x i))` for `x ∈ U₂`.
9. For every unit `c` of `K` with `v c = 1` there is `t ∈ characterValuationKernel v S_K`
   (so `v(χ(t)) = 1` for every rational character `χ` of `S_K`) such that
   * `σ · T_t = T_t` for every `σ ∈ Aut(K/k)` with `σ c = c`;
   * for `x ∈ U`: `T_t x T_t⁻¹ ∈ U` and `q (T_t x T_t⁻¹) = c^d • q x`;
   * for `x ∈ U₂`: `e (T_t x T_t⁻¹) = c^2 • e x`.

The maps `q`, `e` are total functions on `G_K(K)`; only their values on `U`, resp. `U₂`, matter.
Condition 3 says that `q` identifies `U/U₂` with an additive subgroup of `K^n`. Conditions 4–5
say that `e` identifies `U₂` with an additive subgroup of `K^m`.

## Expected source of the data

For a split torus `S` and a root `α` with no multiples `n α` (`n ≥ 3`) among the roots, the
intended witnesses are as follows. `q` is the vector-group coordinate of `U_α/U_{2α}` over `k`,
and `e` the vector-group coordinate of `U_{2α}` over `k` (with `m = 0` if `2α` is not a root).
The point `t` is `ν(c)` for a cocharacter `ν` defined over `k`: the coroot of `2α` with `d = 1`
if `2α` is a root, otherwise the coroot of `α` with `d = 2`. Then `α(ν(c)) = c^d` and
`(2α)(ν(c)) = c^2`.

## Implementation notes

The two local instances `rootGroupLinearization_isAffineHom_baseChange` and
`rootGroupLinearization_isAffineHom_baseChanged` supply `IsAffineHom` for the two definitionally
equal forms of the base change of `G` (`(GroupScheme.baseChange (algebraBaseMap k K)).obj G`,
used by root groups, and `baseChanged k K G`, used by `rationalConjugate`). Both are proved by
unfolding to `pullback.snd G.X.hom _`.
